package boundchecker

import analysis.{Invariant, PredTrans, Z3Solver}
import com.microsoft.z3.BoolExpr
import com.sun.source.tree.{AssignmentTree, MethodTree, Tree, VariableTree}
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.dataflow.cfg.CFGBuilder
import org.checkerframework.dataflow.cfg.block.RegularBlock
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.TreeUtils
import utils.{GraphUtil, MyCFG, Utils}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}
import scala.util.matching.Regex
// import collection.JavaConverters._


/**
  * @author Tianhan Lu
  */
class BoundVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  val DEBUG_VISIT_ASSIGN = false
  val DEBUG_LOCAL_INV = true
  val DEBUG_GLOBAL_INV = true

  var resVarRegex: Regex = """R(\d*)""".r

  var cfgs = new HashMap[MethodTree, MyCFG]()
  var solvers = new HashMap[MethodTree, Z3Solver]
  var localInvs = new HashMap[MethodTree, HashMap[Tree, Set[BoolExpr]]]
  var globalInvs = new HashMap[MethodTree, Set[BoolExpr]]

  override def visitMethod(node: MethodTree, p: Void): Void = {
    val treePath = atypeFactory.getPath(node)
    val classTree = TreeUtils.enclosingClass(treePath)
    assert(classTree != null)

    val z3Solver = solvers.getOrElse(node, new Z3Solver)
    solvers = solvers + (node -> z3Solver)

    try {
      val cfg = CFGBuilder.build(treePath.getCompilationUnit, node, classTree, checker.getContext.getProcessingEnvironment)
      val myCFG = MyCFG(cfg)
      cfgs += node -> myCFG

      if (node.getName.toString != "<init>") {
        // GraphUtil.printCFGtoPDF(cfg, Utils.OUTPUT_DIR)
        GraphUtil.printGraphtoPDF(myCFG.graph, Utils.OUTPUT_DIR + Utils.SEPARATOR + classTree.getSimpleName + "_" + node.getName.toString)
      }

      globalInvs = globalInvs + (node -> Invariant.genNewGlobInv(myCFG.allVars, z3Solver))
    }
    catch {
      case ex: Exception =>
        Utils.printRedString("[Exception] Generate CFG for method: " + TreeUtils.elementFromTree(node).getSimpleName)
        ex.getStackTrace.slice(0, 3).foreach(e => println(e))
      // ex.printStackTrace()
    }
    super.visitMethod(node, p)
  }

  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    val treePath = atypeFactory.getPath(node)
    val enclosingMethod: MethodTree = TreeUtils.enclosingMethod(treePath)
    assert(enclosingMethod != null)

    val z3Solver = solvers.getOrElse(enclosingMethod, new Z3Solver)
    solvers = solvers + (enclosingMethod -> z3Solver)

    // Guess local invariants
    resVarRegex.findFirstIn(node.getVariable.toString) match {
      case Some(resVarName) =>
        cfgs.get(enclosingMethod) match {
          case Some(myCFG) =>
            val blocks = myCFG.graph.vertexSet().asScala.filter({
              case reg: RegularBlock => reg.getContents.asScala.zipWithIndex.exists({
                case (n, idx) =>
                  if (n.getTree == node) {
                    if (idx != reg.getContents.size() - 1)
                      Utils.assertFalse("Resource instruction [" + node.toString + "] must be at the end of a block!")
                    true
                  } else false
              })
              case _ => false
            })
            if (blocks.size != 1) Utils.assertFalse("Multiple/None blocks contain a same resource instruction!")
            val curBlock = blocks.head.asInstanceOf[RegularBlock]
            if (DEBUG_VISIT_ASSIGN) println("Visiting assignment in block: " + curBlock.getId)

            // GraphUtil.printGraph(myCFG.graph)
            val invs = Invariant.inferLocalInv(curBlock, myCFG, z3Solver.mkTrue(), z3Solver)
            if (invs.isEmpty) issueWarning(node, "No invariant is inferred!")

            if (DEBUG_LOCAL_INV) {
              Utils.printRedString("We inferred " + invs.size + " local invariants!")
              invs.foreach(b => Utils.printCyanString(b.toString))
            }

            localInvs.get(enclosingMethod) match {
              case Some(map) =>
                localInvs = localInvs + (enclosingMethod -> (map + (node -> invs)))
              case None =>
                localInvs = localInvs + (enclosingMethod -> HashMap(node -> invs))
            }
          case None => // There is no CFG for the enclosing method
        }
      case None => // This is not an assignment updating resource variables
    }

    // Verify global invariants
    verifyGlobInvs(node, enclosingMethod, z3Solver)

    super.visitAssignment(node, p)
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    val treePath = atypeFactory.getPath(node)
    val enclosingMethod: MethodTree = TreeUtils.enclosingMethod(treePath)
    assert(enclosingMethod != null)

    val z3Solver = solvers.getOrElse(enclosingMethod, new Z3Solver)
    solvers = solvers + (enclosingMethod -> z3Solver)

    // Verify global invariants
    verifyGlobInvs(node, enclosingMethod, z3Solver)

    super.visitVariable(node, p)
  }

  private def issueWarning(node: Object, msg: String): Unit = {
    checker.report(Result.warning(msg), node)
  }

  private def issueError(node: Object, msg: String): Unit = {
    checker.report(Result.failure(msg), node)
  }

  // We only verify inductive global invariants (which is very demanding)
  private def verifyGlobInvs(stmt: Tree, method: MethodTree, z3Solver: Z3Solver): Unit = {
    globalInvs.get(method) match {
      case Some(invs) =>
        val newGlobInvs = invs.foldLeft(new HashSet[BoolExpr])({
          (acc, inv) =>
            val wlp = PredTrans.wlpBasic(stmt, inv, z3Solver)
            val implication = z3Solver.mkImplies(inv, wlp)
            val res = z3Solver.checkSAT(implication)
            if (res) acc + inv
            else acc
        })
        if (DEBUG_GLOBAL_INV) {
          val szUpdate = newGlobInvs.size - invs.size
          Utils.printRedString("We verified " + newGlobInvs.size + " global invariants! # of invalidated invariants is: " + szUpdate)
          newGlobInvs.foreach(b => Utils.printYellowString(b.toString))
        }
        globalInvs = globalInvs + (method -> newGlobInvs)
      case None =>
    }
  }
}