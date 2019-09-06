package boundchecker

import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}

/**
  * @author Tianhan Lu
  */
class BoundAnnotatedTypeFactory (checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  this.postInit()
}
