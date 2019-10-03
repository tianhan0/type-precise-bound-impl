package analysis

import boundchecker.Vars
import com.microsoft.z3.{BoolExpr, Expr, IntExpr}
import com.sun.source.tree.MethodTree
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.Block
import org.checkerframework.javacutil.TreeUtils
import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import utils.{GraphUtil, Utils}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG_SMTLIB = false
  val DEBUG_LOOP_TRAVERSE = false
  val DEBUG_LOCAL_INV = false
  val DEBUG_GEN_NEW_INV = false
  private val INVS_TO_DEBUG = HashSet("(<= (+ (* (- 1) i) R1) 0)")

  var TOTAL_TIME: Double = 0

  var dp = List[(InvGuess, Set[BoolExpr])]()

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferInv(loc: Block,
               graph: Graph[Block, DefaultEdge],
               vars: Vars,
               ctxPred: BoolExpr, // The predicate abstracting the context under which invariants need to be inferred
               z3Solver: Z3Solver,
               indent: Int = 0): Set[BoolExpr] = {
    val start = System.nanoTime()
    val invGuess = InvGuess(loc, graph, ctxPred)
    dp.foreach({
      case (invGuessp, inv) =>
        if (invGuessp.equals(invGuess)) {
          // println("!!!!!!!!!!!!!!!")
          return inv
        }
    })

    val allVars = vars.allVars

    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer invariant right after block " + loc.getId + " started:")

    val invs = genOctagonInv(allVars, z3Solver)
    if (DEBUG_GEN_NEW_INV) println("# of vars: " + allVars.size + "\n# of invs: " + invs.size)
    val validInvs = invs.filter({
      inv =>
        val wlps = PredTrans.wlpProg(graph, inv, loc, z3Solver)
        wlps.forall({
          case (root, wlp) =>
            val implication = if (root == loc) z3Solver.mkImplies(inv, wlp) else z3Solver.mkImplies(z3Solver.mkTrue(), wlp)
            val res = Invariant.checkForall(implication, allVars, z3Solver)
            res._1
        })
    })

    if (DEBUG_LOCAL_INV) {
      println(indentStr + "---Infer invariant right after block " + loc.getId + " finishes.")
      println(indentStr + "---Valid invariants are: " + validInvs.foldLeft("\n")((acc, b) => acc + indentStr + "  " + b + "\n"))
    }

    dp = (InvGuess(loc, graph, ctxPred), validInvs) :: dp
    val end = System.nanoTime()
    TOTAL_TIME += (end - start).toDouble / Utils.NANO

    validInvs
  }

  def getTyp(typ: TypeMirror): TypeKind = {
    if (typ.getKind == TypeKind.INT) TypeKind.INT
    else if (typ.getKind == TypeKind.BOOLEAN) TypeKind.BOOLEAN
    else {
      assert(false)
      TypeKind.INT
    }
  }

  def genOctagonInv(vars: Set[Expr], z3Solver: Z3Solver): Set[BoolExpr] = {
    val coeff = HashSet[Int](-1, 1)
    val constants = {
      val pos = HashSet[Int](0)
      pos.map(n => -n) ++ pos
    }

    vars.zipWithIndex.foldLeft(new HashMap[String, BoolExpr])({
      case (acc, (var1, idx1)) =>
        vars.zipWithIndex.foldLeft(acc)({
          case (accp, (var2, idx2)) =>
            if (idx2 > idx1) {
              (var1, var2) match {
                case (var1: IntExpr, var2: IntExpr) =>
                  coeff.foldLeft(accp)({
                    (acc1, c1) =>
                      coeff.foldLeft(acc1)({
                        (acc2, c2) =>
                          constants.foldLeft(acc2)({
                            (acc3, c3) =>
                              if (c1 < 0 && c2 < 0) acc3
                              else {
                                val add = z3Solver.mkAdd(
                                  if (c1 == 1) var1 else z3Solver.mkMul(z3Solver.mkIntVal(c1), var1),
                                  if (c2 == 1) var2 else z3Solver.mkMul(z3Solver.mkIntVal(c2), var2)
                                )
                                val le = z3Solver.mkLe(add, z3Solver.mkIntVal(c3))
                                val lt = z3Solver.mkLt(add, z3Solver.mkIntVal(c3))

                                (Utils.getResVarName(var1.toString), Utils.getResVarName(var2.toString)) match {
                                  case (Some(_), Some(_)) =>
                                    acc3 + (le.toString -> le) + (lt.toString -> lt)
                                  case (Some(_), None) =>
                                    // acc3 + (le.toString -> le) + (lt.toString -> lt)
                                    if (c1 < 0) acc3
                                    else acc3 + (le.toString -> le) + (lt.toString -> lt)
                                  case (None, Some(_)) =>
                                    // acc3 + (le.toString -> le) + (lt.toString -> lt)
                                    if (c2 < 0) acc3
                                    else acc3 + (le.toString -> le) + (lt.toString -> lt)
                                  case (None, None) =>
                                    acc3 + (le.toString -> le) + (lt.toString -> lt)
                                }
                              }
                          })
                      })
                  })
                case _ => accp
              }
            }
            else accp
        })
    }).values.toSet + z3Solver.mkTrue()
    /*else {
      // When debugging using this branch, keep in mind that while the following invariant will be included
      // in all invocation to this method, if we are not using this branch, the following invariant might not
      // be included in all invocation to this method!
      HashSet[BoolExpr](
        z3Solver.mkLe(
          z3Solver.mkAdd(
            z3Solver.mkMul(z3Solver.mkIntVal(1), z3Solver.mkIntVar("i")),
            z3Solver.mkMul(z3Solver.mkIntVal(-1), z3Solver.mkIntVar("n"))
          ),
          z3Solver.mkIntVal(0))
      )
    }*/
  }

  def genIntervalInv(allVars: Set[(String, TypeMirror)], z3Solver: Z3Solver): Set[BoolExpr] = {
    val constants = {
      val pos = HashSet[Int](0, 1)
      pos.map(n => -n) ++ pos
    }
    allVars.foldLeft(new HashSet[BoolExpr])({
      case (acc, (name, typ)) =>
        if (getTyp(typ) == TypeKind.INT) acc + z3Solver.mkGe(z3Solver.mkIntVar(name), z3Solver.mkIntVal(0))
        else acc
    })
  }

  def genBounds(vars: Vars, z3Solver: Z3Solver): Set[BoolExpr] = {
    val sumR = {
      if (vars.resVars.isEmpty) z3Solver.mkIntVal(0)
      else if (vars.resVars.size == 1) vars.resVars.head
      else z3Solver.mkAdd(vars.resVars.toArray: _*)
    }
    val sumIn: Expr = {
      val intArgs = vars.args.filter(arg => arg.isInstanceOf[IntExpr])
      // assert(intArgs.isEmpty, "The method doesn't have any int-typed arguments!")
      z3Solver.mkAdd(intArgs.toArray: _*)
    }
    val rhses = {
      Seq.range(1, 3).foldLeft(new HashSet[Expr])({
        (acc, coeff) =>
          acc + Seq.range(1, coeff).foldLeft(sumIn)((acc, i) => z3Solver.mkAdd(acc, sumIn))
      })
    }
    rhses.foldLeft(new HashSet[BoolExpr])((acc, rhs) => acc + z3Solver.mkLe(sumR, rhs))
  }

  def getMethodVars(methodTree: MethodTree, allVars: Set[(String, TypeMirror)], z3Solver: Z3Solver): Vars = {
    val (args: Set[Expr], globVarNames: Set[String]) = methodTree.getParameters.asScala.foldLeft(HashSet[Expr](), HashSet(Utils.BOUND_STR))({
      (acc, variableTree) =>
        val name = variableTree.getName.toString
        val typ = TreeUtils.typeOf(variableTree.getType)
        val variable = {
          if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
          else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
          else {
            assert(false)
            z3Solver.mkFalse()
          }
        }
        (acc._1 + variable, acc._2 + name)
    })

    val (localVars: Set[Expr], resVars: Set[Expr]) = allVars.foldLeft(HashSet[Expr](), HashSet[Expr]())({
      case (acc, (name, typ)) =>
        Utils.getResVarName(name) match {
          case Some(v) =>
            assert(typ.getKind == TypeKind.INT, "Resource variables should be int-typed!")
            (acc._1, acc._2 + z3Solver.mkIntVar(name))
          case _ =>
            if (!globVarNames.contains(name)) {
              val variable = if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
              else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
              else {
                assert(false)
                z3Solver.mkFalse()
              }
              (acc._1 + variable, acc._2)
            }
            else acc
        }
    })
    assert(localVars.intersect(resVars ++ args).isEmpty)
    Vars(localVars, args, resVars)
  }

  // Return true if the assertion is valid
  def checkForall(assertion: BoolExpr, allVars: Set[Expr], z3Solver: Z3Solver): (Boolean, BoolExpr) = {
    val toCheck = {
      z3Solver.mkNot(
        z3Solver.mkForall(allVars.toArray, assertion)
      )
    }
    val res = z3Solver.checkSAT(toCheck)
    (!res, toCheck)
  }

  def getConjunction(invs: Iterable[BoolExpr], z3Solver: Z3Solver): Expr = {
    if (invs.isEmpty) z3Solver.mkTrue()
    else if (invs.size == 1) invs.head
    else z3Solver.mkAnd(invs.toSeq: _*)
  }

  def printTime(): Unit = Utils.printRedString("Local invariant inference's total time is: " + ("%.3f" format TOTAL_TIME) + "s")
}

case class InvGuess(loc: Block, graph: Graph[Block, DefaultEdge], ctxPred: BoolExpr) {
  override def equals(obj: Any): Boolean = {
    obj match {
      case guess: InvGuess =>
        val r1 = loc == guess.loc
        val r2 = GraphUtil.isSameGraph(graph, guess.graph)
        val r3 = ctxPred.toString == guess.ctxPred.toString
        r1 && r2 && r3
      case _ => false
    }
  }
}