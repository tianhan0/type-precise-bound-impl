package boundchecker

import com.sun.source.tree.{AssertTree, AssignmentTree, MethodTree, VariableTree}
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.dataflow.cfg.CFGBuilder
import org.checkerframework.dataflow.cfg.block.{ConditionalBlock, ExceptionBlock, RegularBlock, SpecialBlock}
import org.checkerframework.javacutil.TreeUtils
import utils.{MyCFG, PrintStuff}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashMap
import scala.util.matching.Regex
// import collection.JavaConverters._


/**
  * @author Tianhan Lu
  */
class BoundVisitor (checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  var resVarRegex: Regex = """R(\d+)""".r
  var cfgs = new HashMap[MethodTree, MyCFG]()

  override def visitMethod(node: MethodTree, p: Void): Void = {
    val treePath = atypeFactory.getPath(node)
    val classTree = TreeUtils.enclosingClass(treePath)
    assert(classTree != null)
    try {
      val cfg = CFGBuilder.build(treePath.getCompilationUnit, node, classTree, checker.getContext.getProcessingEnvironment)
      val myCFG = MyCFG(cfg)
      cfgs += node -> myCFG
      // GraphUtil.printCFGtoPDF(cfg, "/Users/lumber/Desktop")
      myCFG.cycles.foreach(cycle => println(cycle.size, cycle.map(b => b.getId)))
    } catch {
      case ex: Exception =>
        PrintStuff.printRedString("[Exception] Generate CFG for method: "+TreeUtils.elementFromTree(node).getSimpleName)
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
          case Some(cfg) =>
            cfg.cfg.getAllBlocks.asScala.foreach({
              case reg: RegularBlock =>
                reg.getContents.asScala.foreach(n => {
                  n.getTree match {
                    case tree: VariableTree =>
                    case tree: AssignmentTree =>
                      // println(tree)
                    case tree: AssertTree =>
                      // println(tree)
                    case _ =>
                  }
                })
                // if (!reg.isEmpty) println()
              case cond: ConditionalBlock =>
                // println(cond.getThenFlowRule)
              case special: SpecialBlock =>
              case exception: ExceptionBlock =>
              case _ => assert(false)
            })
          case None =>
        }
      case None =>
    }
    super.visitAssignment(node, p)
  }
}