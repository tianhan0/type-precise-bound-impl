package boundchecker

import analysis.{Invariant, Z3Solver}
import com.sun.source.tree.{AssignmentTree, MethodTree}
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.dataflow.cfg.CFGBuilder
import org.checkerframework.dataflow.cfg.block.RegularBlock
import org.checkerframework.javacutil.TreeUtils
import utils.{GraphUtil, MyCFG, Utils}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashMap
import scala.util.matching.Regex
// import collection.JavaConverters._


/**
  * @author Tianhan Lu
  */
class BoundVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  var resVarRegex: Regex = """R(\d*)""".r
  var cfgs = new HashMap[MethodTree, MyCFG]()
  val DEBUG_VISIT_ASSIGN = false

  override def visitMethod(node: MethodTree, p: Void): Void = {
    val treePath = atypeFactory.getPath(node)
    val classTree = TreeUtils.enclosingClass(treePath)
    assert(classTree != null)
    try {
      val cfg = CFGBuilder.build(treePath.getCompilationUnit, node, classTree, checker.getContext.getProcessingEnvironment)
      val myCFG = MyCFG(cfg)
      cfgs += node -> myCFG
      if (node.getName.toString != "_init") GraphUtil.printCFGtoPDF(cfg, "/Users/lumber/Desktop/outputs")
    } catch {
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
    resVarRegex.findFirstIn(node.getVariable.toString) match {
      case Some(resVarName) =>
        cfgs.get(enclosingMethod) match {
          case Some(myCFG) =>
            val blocks = myCFG.graph.vertexSet().asScala.filter({
              case reg: RegularBlock => reg.getContents.asScala.zipWithIndex.exists({
                case (n, idx) =>
                  if (n.getTree == node) {
                    if (idx != reg.getContents.size() - 1)
                      Utils.assertFalse("Resource instruction ["+node.toString+"] must be at the end of a block!")
                    true
                  } else false
              })
              case _ => false
            })
            if (blocks.size != 1) Utils.assertFalse("Multiple/None blocks contain a same resource instruction!")
            val curBlock = blocks.head.asInstanceOf[RegularBlock]
            if (DEBUG_VISIT_ASSIGN) println("Visiting assignment in block: " + curBlock.getId)

            // GraphUtil.printGraph(myCFG.graph)
            val z3Solver = new Z3Solver
            Invariant.inferLocalInv(curBlock, myCFG.graph, z3Solver.mkTrue(), z3Solver)
          case None => // There is no CFG for the enclosing method
        }
      case None => // This is not an assignment updating resource variables
    }
    super.visitAssignment(node, p)
  }
}