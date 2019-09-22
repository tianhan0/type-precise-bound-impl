package boundchecker

import analysis.{Invariant, PredTrans, Z3Solver}
import com.microsoft.z3.{BoolExpr, Expr}
import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.dataflow.cfg.CFGBuilder
import org.checkerframework.dataflow.cfg.block.RegularBlock
import org.checkerframework.framework.source.Result
import org.checkerframework.javacutil.TreeUtils
import utils.{GraphUtil, MyCFG, Utils}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}
// import collection.JavaConverters._


/**
  * @author Tianhan Lu
  */
class BoundVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  val DEBUG_VISIT_ASSIGN = false
  val DEBUG_LOCAL_INV = true
  val DEBUG_GLOBAL_INV = false
  val DEBUG_VERIFICATION = true

  var cfgs = new HashMap[MethodTree, MyCFG]()
  var solvers = new HashMap[MethodTree, Z3Solver]
  var localInvs = new HashMap[MethodTree, HashMap[Tree, Set[BoolExpr]]]
  var globalInvs = new HashMap[MethodTree, Set[BoolExpr]]
  var assumptions = new HashMap[MethodTree, Set[BoolExpr]] // Additional unchecked global invariants
  var bounds = new HashMap[MethodTree, Set[BoolExpr]]
  var vars = new HashMap[MethodTree, Vars]

  Runtime.getRuntime.addShutdownHook(new Thread() {
    override def run(): Unit = {
      checkBound()
      Z3Solver.printTime()
      Invariant.printTime()
    }

    // Reference: SourceChecker.typeProcessingStart
  })

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

      globalInvs = globalInvs + (node -> Invariant.guessGlobInv(GraphUtil.getProgAllVars(myCFG.graph), z3Solver))

      val myVars = Invariant.getMethodVars(node, myCFG.allVars, z3Solver)

      vars = vars + (node -> myVars)

      if (myVars.args.nonEmpty && myVars.resVars.nonEmpty) {
        bounds = bounds + (node -> Invariant.guessBounds(myVars, z3Solver))
      }
      else {
        println("We don't verify bounds for method " + node.getName + ", because it does not contain resource variables or method arguments")
      }
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
    val (myCFG, z3Solver, enclosingMethod) = prep(node)

    // Guess local invariants
    Utils.getResVarName(node.getVariable.toString) match {
      case Some(resVarName) =>
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
        val invs = Invariant.inferLocalInv(curBlock, myCFG.graph, GraphUtil.getProgAllVars(myCFG.graph), z3Solver.mkTrue(), z3Solver)
        if (invs.isEmpty) issueWarning(node, "No invariant is inferred!")

        if (DEBUG_LOCAL_INV) {
          Utils.printRedString("\nWe inferred " + invs.size + " local invariants!")
          invs.foreach(b => Utils.printCyanString(b.toString))
          println()
        }

        localInvs.get(enclosingMethod) match {
          case Some(map) =>
            localInvs = localInvs + (enclosingMethod -> (map + (node -> invs)))
          case None =>
            localInvs = localInvs + (enclosingMethod -> HashMap(node -> invs))
        }
      case None => // This is not an assignment updating resource variables
    }

    // Verify global invariants
    verifyGlobInvs(node, enclosingMethod, myCFG, z3Solver)

    super.visitAssignment(node, p)
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    val (myCFG, z3Solver, enclosingMethod) = prep(node)

    // Verify global invariants
    verifyGlobInvs(node, enclosingMethod, myCFG, z3Solver)

    super.visitVariable(node, p)
  }

  override def visitAssert(node: AssertTree, p: Void): Void = {
    val (myCFG, z3solver, enclosingMethod) = prep(node)

    if (node.getDetail != null) {
      assert(node.getCondition != null)
      val expr = PredTrans.transExpr(node.getCondition, z3solver).asInstanceOf[BoolExpr]

      if (node.getDetail.toString == "\"" + Utils.BOUND_STR + "\"") {
        bounds.get(enclosingMethod) match {
          case Some(set) => bounds = bounds + (enclosingMethod -> (set + expr))
          case None => bounds = bounds + (enclosingMethod -> HashSet(expr))
        }
      }
      else if (node.getDetail.toString == "\"" + Utils.GLOBAL_STR + "\"") {
        assumptions.get(enclosingMethod) match {
          case Some(set) => assumptions = assumptions + (enclosingMethod -> (set + expr))
          case None => assumptions = assumptions + (enclosingMethod -> HashSet(expr))
        }
      }
    }
    super.visitAssert(node, p)
  }

  private def prep(node: Tree): (MyCFG, Z3Solver, MethodTree) = {
    val treePath = atypeFactory.getPath(node)
    val enclosingMethod: MethodTree = TreeUtils.enclosingMethod(treePath)
    assert(enclosingMethod != null)

    val z3Solver = solvers.getOrElse(enclosingMethod, new Z3Solver)
    solvers = solvers + (enclosingMethod -> z3Solver)

    val myCFG: MyCFG = cfgs.getOrElse(enclosingMethod, null)
    assert(myCFG != null)

    (myCFG, z3Solver, enclosingMethod)
  }

  private def issueWarning(node: Object, msg: String): Unit = {
    checker.report(Result.warning(msg), node)
  }

  private def issueError(node: Object, msg: String): Unit = {
    checker.report(Result.failure(msg), node)
  }

  // We only verify inductive global invariants (which is very demanding)
  private def verifyGlobInvs(stmt: Tree, method: MethodTree, myCFG: MyCFG, z3Solver: Z3Solver): Unit = {
    stmt match {
      case tree@(_: BlockTree | _: DoWhileLoopTree | _: EnhancedForLoopTree | _: ForLoopTree | _: IfTree | _: SwitchTree | _: SynchronizedTree | _: ThrowTree | _: TryTree | _: WhileLoopTree) => assert(false, "Should be an atomic statement!")
      case _ =>
    }
    // Reference: https://stackoverflow.com/questions/52645036/scala-syntax-to-match-on-multiple-case-class-types-without-decomposing-the-case

    globalInvs.get(method) match {
      case Some(invs) =>
        val newGlobInvs = invs.foldLeft(new HashSet[BoolExpr])({
          (acc, inv) =>
            val wlp = PredTrans.wlpBasic(stmt, inv, z3Solver)
            val implication = z3Solver.mkImplies(inv, wlp)
            val res = Invariant.checkForall(implication, myCFG.allVars, z3Solver)
            if (res._1) acc + inv
            else acc
        })
        if (DEBUG_GLOBAL_INV) {
          val szUpdate = invs.size - newGlobInvs.size
          Utils.printRedString("We verified " + newGlobInvs.size + " global invariants! # of invalidated invariants is: " + szUpdate)
          newGlobInvs.foreach(b => Utils.printYellowString(b.toString))
        }
        globalInvs = globalInvs + (method -> newGlobInvs)
      case None =>
    }
  }

  def checkBound(): Unit = {
    if (bounds.nonEmpty) println("\n\n\nBound verification starts:")

    bounds.foreach({
      case (methodTree, bounds1) =>
        val z3Solver = solvers.getOrElse(methodTree, new Z3Solver)
        val myCFG: MyCFG = cfgs.getOrElse(methodTree, null)
        assert(myCFG != null)

        val (localVars: Set[Expr], globalVars: Set[Expr]) = {
          vars.get(methodTree) match {
            case Some(v) => (v.locals, v.args ++ v.resVars)
            case None =>
              assert(false, "Method " + methodTree.getName.toString + " doesn't have any variables!")
              (HashSet[Expr](), HashSet[Expr]())
          }
        }

        val globals = {
          val g = globalInvs.get(methodTree) match {
            case Some(invs) => Invariant.getConjunction(invs, z3Solver)
            case None => z3Solver.mkTrue()
          }
          val a = assumptions.get(methodTree) match {
            case Some(invs) => Invariant.getConjunction(invs, z3Solver)
            case None => z3Solver.mkTrue()
          }
          z3Solver.mkAnd(g, a)
        }

        val locals = {
          localInvs.get(methodTree) match {
            case Some(map) =>
              map.foldLeft(z3Solver.mkTrue())({
                case (acc, (tree, invs)) =>
                  val l = Invariant.getConjunction(invs, z3Solver)
                  val exists = {
                    val body = z3Solver.mkAnd(l, globals)
                    if (localVars.isEmpty) body
                    else z3Solver.mkExists(localVars.toArray, body)
                  }
                  z3Solver.mkAnd(acc, exists)
              })
            case None => z3Solver.mkTrue()
          }
        }

        bounds1.foreach(bound => {
          val toCheck = z3Solver.mkForall(
            globalVars.toArray,
            z3Solver.mkImplies(locals, bound)
          )
          if (DEBUG_VERIFICATION) println(toCheck.toString)

          val res = z3Solver.checkSAT(toCheck)
          if (res) Utils.printGreenString("Bound " + bound.toString + " for method " + methodTree.getName + " is verified!\n")
          else Utils.printRedString("Bound " + bound.toString + " for method " + methodTree.getName + " is not verified!\n")
        })
    })
  }
}

case class Vars(locals: Set[Expr], args: Set[Expr], resVars: Set[Expr])