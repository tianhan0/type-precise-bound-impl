package boundchecker

import com.sun.source.tree.{BlockTree, MethodInvocationTree}
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}
import scala.collection.JavaConversions._

/**
  * @author Tianhan Lu
  */
class BoundVisitor (checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    super.visitMethodInvocation(node, p)
  }

  override def visitBlock(blockTree: BlockTree, p: Void): Void = {
    blockTree.getStatements.foreach {
      stmt => println(stmt)
    }

    super.visitBlock(blockTree, p)
  }
}