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
  val DEBUG_VERIFICATION = false

  var cfgs = new HashMap[MethodTree, MyCFG]()
  var solvers = new HashMap[MethodTree, Z3Solver]
  var localInvs = new HashMap[MethodTree, HashMap[Tree, Set[BoolExpr]]]
  var globalInvs = new HashMap[MethodTree, Set[BoolExpr]]
  var assumptions = new HashMap[MethodTree, Set[BoolExpr]] // Additional unchecked global invariants
  var bounds = new HashMap[MethodTree, Set[BoolExpr]]
  var vars = new HashMap[MethodTree, Vars]
  var results = new HashSet[BndResult]

  val MAX_NUM_OF_LOCAL_INVS = 16

  // sys.addShutdownHook(checkBound())
  // Reference: SourceChecker.typeProcessingStart

  override def processClassTree(classTree: ClassTree): Unit = {
    super.processClassTree(classTree)

    println()
    val verifiedBounds = results.filter(res => res.isSuccessful)
    Utils.printYellowString("# of methods that are successfully verified with bounds are " + verifiedBounds.size + " out of " + results.size)
    if (verifiedBounds.nonEmpty) {
      Utils.printYellowString("Below are these methods:")
      verifiedBounds.foreach(res => Utils.printYellowString(res.methodTree.getName.toString))
    }
    println()
    Z3Solver.printTime()
    Invariant.printTime()
  }

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
        val guesses = Invariant.guessBounds(myVars, z3Solver)
        bounds = bounds + (node -> guesses)
        println("\nWe attempt to automatically verify " + guesses.size + " bound(s) for method " + node.getName)
      }
      else {
        println("\nWe did not attempt to verify bounds for method " + node.getName + ", because it does not contain resource variables or method arguments")
      }
    }
    catch {
      case ex: Exception =>
        Utils.printRedString("[Exception] Generate CFG for method: " + TreeUtils.elementFromTree(node).getSimpleName)
        ex.getStackTrace.slice(0, 3).foreach(e => println(e))
      // ex.printStackTrace()
    }
    super.visitMethod(node, p)

    checkBound(node)
    null
  }

  override def visitAssignment(node: AssignmentTree, p: Void): Void = {
    val (myCFG, z3Solver, enclosingMethod, vars) = prep(node)

    // Guess local invariants
    Utils.getResVarName(node.getVariable.toString) match {
      case Some(resVarName) =>
        val blocks = myCFG.graph.vertexSet().asScala.filter({
          case reg: RegularBlock => reg.getContents.asScala.zipWithIndex.exists({
            case (n, idx) =>
              if (n.getTree == node) {
                if (idx != reg.getContents.size() - 1)
                  assert(false, "Resource instruction [" + node.toString + "] must be at the end of a block!")
                true
              } else false
          })
          case _ => false
        })
        if (blocks.size != 1) assert(false, "Multiple/None blocks contain a same resource instruction!")
        val curBlock = blocks.head.asInstanceOf[RegularBlock]
        if (DEBUG_VISIT_ASSIGN) println("Visiting assignment in block: " + curBlock.getId)

        // GraphUtil.printGraph(myCFG.graph)
        val invs = Invariant.inferLocalInv(curBlock, myCFG.graph, vars, z3Solver.mkTrue(), true, z3Solver)
        if (invs.isEmpty) issueWarning(node, "No invariant is inferred!")

        if (DEBUG_LOCAL_INV) {
          Utils.printYellowString("\nWe inferred " + invs.size + " local invariants at line " + Utils.getLineNumber(node, positions, root))
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
    verifyGlobInvs(node, enclosingMethod, myCFG, z3Solver, vars)

    super.visitAssignment(node, p)
  }

  override def visitVariable(node: VariableTree, p: Void): Void = {
    val (myCFG, z3Solver, enclosingMethod, vars) = prep(node)

    // Verify global invariants
    verifyGlobInvs(node, enclosingMethod, myCFG, z3Solver, vars)

    super.visitVariable(node, p)
  }

  override def visitAssert(node: AssertTree, p: Void): Void = {
    val (myCFG, z3solver, enclosingMethod, vars) = prep(node)

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

  private def prep(node: Tree): (MyCFG, Z3Solver, MethodTree, Vars) = {
    val treePath = atypeFactory.getPath(node)
    val enclosingMethod: MethodTree = TreeUtils.enclosingMethod(treePath)
    assert(enclosingMethod != null)

    val z3Solver = solvers.getOrElse(enclosingMethod, new Z3Solver)
    solvers = solvers + (enclosingMethod -> z3Solver)

    val myCFG: MyCFG = cfgs.getOrElse(enclosingMethod, null)
    assert(myCFG != null)

    val vars = this.vars.getOrElse(enclosingMethod, null)
    assert(vars != null)

    (myCFG, z3Solver, enclosingMethod, vars)
  }

  private def issueWarning(node: Object, msg: String): Unit = {
    checker.report(Result.warning(msg), node)
  }

  private def issueError(node: Object, msg: String): Unit = {
    checker.report(Result.failure(msg), node)
  }

  // We only verify inductive global invariants (which is very demanding)
  private def verifyGlobInvs(stmt: Tree, method: MethodTree, myCFG: MyCFG, z3Solver: Z3Solver, vars: Vars): Unit = {
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
            val res = Invariant.checkForall(implication, vars.allVars, z3Solver)
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

  def checkBound(node: MethodTree): Unit = {
    if (this.bounds.nonEmpty) println("===============================================\nBound verification starts for method " + node.getName.toString + "...")

    this.bounds.filter(m => m._1 == node).foreach({
      case (methodTree, bounds1) =>
        val z3Solver = solvers.getOrElse(methodTree, new Z3Solver)
        val myCFG: MyCFG = cfgs.getOrElse(methodTree, null)
        assert(myCFG != null)

        val vars = this.vars.getOrElse(methodTree, null)
        assert(vars != null || vars.allVars.isEmpty, "Method " + methodTree.getName.toString + " doesn't have any variables!")
        val (localVars, globalVars) = (vars.locals, vars.args ++ vars.resVars)

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

        localInvs.get(methodTree) match {
          case Some(map) =>
            // Each subset is a set of local invariants
            val locals: Iterator[Set[BoolExpr]] = {
              /*val locals = map.foldLeft(new HashSet[BoolExpr])({
                case (acc, (node: Tree, locals: Set[BoolExpr])) =>
                  val localsCompatibleWithGlobals = locals.filter({
                    local =>
                      val forall = {

                        val body = z3Solver.mkImplies(globals, local)
                        // Check if there exists an assignment to all variables such that the conjunction of the current
                        // local invariant and global invariants are SAT, because the verified local invariants
                        // may contradict global invariants (i.e. there exists no state that both satisfy
                        // local and global invariants), in which case we will have `false=>anything`.
                        z3Solver.mkForall(vars.allVars.toArray, body) // TODO: all variables or global variables or ???
                      }
                      val res = z3Solver.checkSAT(forall)
                      res
                  })
                  acc ++ localsCompatibleWithGlobals
              })*/
              val locals = map.values.flatten.toSet
              // Limit the # of local invariants that we use
              if (locals.size > MAX_NUM_OF_LOCAL_INVS) {
                Utils.printYellowString("Truncating the # of local invariants from " + locals.size + " into " + MAX_NUM_OF_LOCAL_INVS + "...")
                locals.slice(0, MAX_NUM_OF_LOCAL_INVS).subsets()
              }
              else locals.subsets()
              // Utils.power(locals)
              // Error "java.lang.NoClassDefFoundError: scala/collection/SetLike$$anon$1" is caused by invoking
              // XXX.subset(). The error is fixed by implementing power set generation
              // References:
              // https://github.com/ztellman/aleph/issues/320#issuecomment-304113405
              // https://stackoverflow.com/questions/11351633/java-scala-shutdown-hook-noclassdeffounderror
            }

            val exists = {
              locals.foldLeft(new HashSet[Expr])({
                (acc, subset) =>
                  val l = Invariant.getConjunction(subset, z3Solver)
                  val body = z3Solver.mkAnd(l, globals)
                  val exist = {
                    if (localVars.isEmpty) body
                    else z3Solver.mkExists(localVars.toArray, body)
                  }
                  val res = z3Solver.checkSAT(exist)
                  if (res) acc + exist
                  else {
                    acc
                  }
              })
            }

            val (success: Set[Expr], failure: Set[Expr]) = bounds1.foldLeft((HashSet[Expr](), HashSet[Expr]()))({
              (acc3, bound) =>
                exists.foldLeft(acc3)({
                  (acc4, exist) =>
                    // We check a new assertion only if all previous checks failed
                    // if (acc4._1.isEmpty) {
                    val toCheck = {
                      z3Solver.mkForall(
                        globalVars.toArray,
                        // We should use `implication` here (instead of `and`), because we don't expect all inputs
                        // to satisfy both invariants and bounds. We only care if those program states that
                        // satisfy invariants also satisfy bounds
                        z3Solver.mkImplies(exist, bound)
                      )
                    }

                    val res = z3Solver.checkSAT(toCheck)
                    if (DEBUG_VERIFICATION) println("\n" + res + "\n" + toCheck.toString)
                    if (res) (acc4._1 + bound, acc4._2)
                    else (acc4._1, acc4._2 + bound)
                  // }
                  // else acc4
                })
            })

            if (bounds1.nonEmpty) {
              val bndRes = BndResult(methodTree, success, failure)
              bndRes.printResults()
              results = results + bndRes
            }
          case None =>
        }
    })
  }
}

case class Vars(locals: Set[Expr], args: Set[Expr], resVars: Set[Expr]) {
  val allVars: Set[Expr] = locals ++ args ++ resVars
}

case class BndResult(methodTree: MethodTree, success: Set[Expr], failure: Set[Expr]) {
  val isSuccessful: Boolean = success.nonEmpty

  def printResults(): Unit = {
    val methodName = methodTree.getName.toString
    println("\nResults for method " + methodName)
    if (success.nonEmpty) {
      success.foreach(bound => Utils.printGreenString("[success] Bound " + bound.toString + " for method " + methodName + " is verified"))
    }
    else if (success.isEmpty) {
      assert(failure.nonEmpty)
      failure.foreach(bound => Utils.printRedString("[failure] Bound " + bound.toString + " for method " + methodName + " is not verified"))
    }
  }
}