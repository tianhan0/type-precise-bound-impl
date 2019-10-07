package analysis

import boundchecker.Vars
import com.microsoft.z3.{BoolExpr, Expr, IntExpr}
import com.sun.source.tree.MethodTree
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.SpecialBlock.SpecialBlockType
import org.checkerframework.dataflow.cfg.block.{Block, ConditionalBlock, SpecialBlockImpl}
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
  val DEBUG_GEN_NEW_INV = true
  private val INVS_TO_DEBUG = HashSet("(<= (+ (* (- 1) i) R1) 0)")

  val MAX_NUM_OF_INV = 3
  val MAX_NUM_OF_LOOP_INV = 2

  var TOTAL_TIME_INV: Double = 0
  var TOTAL_TIME_LOOP_INV: Double = 0

  var dp1 = List[(InvGuess, Set[BoolExpr])]()
  var dp2 = List[(LoopInvGuess, Set[BoolExpr])]()

  def inferInv(loc: Block,
               graph: Graph[Block, DefaultEdge],
               vars: Vars,
               z3Solver: Z3Solver,
               indent: Int = 0): Set[BoolExpr] = {
    val start = System.nanoTime()
    val invGuess = InvGuess(loc, graph)
    dp1.foreach({
      case (invGuess_p, inv) =>
        if (invGuess_p.equals(invGuess)) {
          // println("!!!!!!!!!!!!!!!")
          return inv
        }
    })

    val roots = graph.vertexSet().asScala.filter(b => graph.inDegreeOf(b) == 0)
    assert(roots.size == 1)
    val root = roots.head

    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer invariant right after block " + loc.getId + " started:")

    val allVars = vars.allVars
    // Generate arbitrary conjunction of the above invariants
    val allInvs: Set[BoolExpr] = genOctagonInv(allVars, z3Solver).subsets()
      .filter(set => set.size <= MAX_NUM_OF_INV)
      .map(set => Invariant.getConjunction(set, z3Solver)).toSet
    val invs = {
      // val invs = removeFalseInvs(allInvs, allVars, z3Solver)
      // removeWeakInvs(invs, allVars, z3Solver)
      // TODO: Only guess invariants about variables used or defined in the current program? Not sufficient for the Zulger example
      allInvs
    }

    if (DEBUG_GEN_NEW_INV) println("[Inv] # of vars: " + allVars.size + "; # of invs: " + invs.size)
    val validInvs = invs.filter({
      inv =>
        PredTrans.wlpProg(graph, inv, root, loc, vars, z3Solver).get(root) match {
          case Some(wlp) =>
            val implication = z3Solver.mkImplies(z3Solver.mkTrue(), wlp)
            val r1 = Invariant.checkForall(implication, allVars, z3Solver)
            // println(root.getId, loc.getId, root == loc, roots.contains(root))
            /*if (!r1._1) {
              println(inv)
              println(r1)
              println()
            }*/

            val newGraph = GraphUtil.cloneGraph(graph)
            val newRoot = new SpecialBlockImpl(SpecialBlockType.ENTRY)
            newGraph.addVertex(newRoot)
            val outEdges = newGraph.outgoingEdgesOf(loc).asScala.toList
            val succNodes = outEdges.map(e => newGraph.getEdgeTarget(e))
            succNodes.foreach(n => newGraph.addEdge(newRoot, n))
            newGraph.removeAllEdges(outEdges.asJava)

            PredTrans.wlpProg(newGraph, inv, newRoot, loc, vars, z3Solver).get(newRoot) match {
              case Some(wlp2) =>
                val implication = z3Solver.mkImplies(inv, wlp2)
                val r2 = Invariant.checkForall(implication, allVars, z3Solver)
                /*if (!r2._1) {
                  println(inv)
                  println(r2)
                  println()
                }*/
                r1._1 && r2._1
              case None => false
            }
          case None => false
        }
    })

    if (DEBUG_LOCAL_INV) {
      println(indentStr + "---Infer invariant right after block " + loc.getId + " finishes.")
      println(indentStr + "---Valid invariants are: " + validInvs.foldLeft("\n")((acc, b) => acc + indentStr + "  " + b + "\n"))
    }

    dp1 = (invGuess, validInvs) :: dp1
    val end = System.nanoTime()
    TOTAL_TIME_INV += (end - start).toDouble / Utils.NANO

    // Invariant.removeWeakInvs(validInvs, allVars, z3Solver)
    validInvs
  }

  def inferLoopInv(loopHead: ConditionalBlock,
                   loopCond: Expr,
                   graph: Graph[Block, DefaultEdge],
                   vars: Vars,
                   z3Solver: Z3Solver,
                   indent: Int = 0): Set[BoolExpr] = {
    val start = System.nanoTime()
    val invGuess = LoopInvGuess(loopHead, loopCond, graph)
    dp2.foreach({
      case (invGuess_p, inv) =>
        if (invGuess_p.equals(invGuess)) {
          return inv
        }
    })

    val newGraph = GraphUtil.cloneGraph(graph)
    val exitBlk = new SpecialBlockImpl(SpecialBlockType.EXIT)
    newGraph.addVertex(exitBlk)
    val backEdges = newGraph.incomingEdgesOf(loopHead).asScala.toList
    val exitNodes = backEdges.map(e => newGraph.getEdgeSource(e))
    exitNodes.foreach(n => newGraph.addEdge(n, exitBlk))
    newGraph.removeAllEdges(backEdges.asJava)

    val allVars = vars.allVars
    val allInvs = genOctagonInv(allVars, z3Solver).subsets()
      .filter(set => set.size <= MAX_NUM_OF_LOOP_INV)
      .map(set => Invariant.getConjunction(set, z3Solver)).toSet
    val invs = {
      // val invs = removeFalseInvs(allInvs, allVars, z3Solver)
      // removeWeakInvs(invs, allVars, z3Solver)
      allInvs
    }

    if (DEBUG_GEN_NEW_INV) println("[LoopInv] # of vars: " + allVars.size + "; # of invs: " + invs.size)
    val validInvs = invs.filter({
      inv =>
        PredTrans.wlpProg(newGraph, inv, loopHead, exitBlk, vars, z3Solver).get(loopHead) match {
          case Some(wlp) =>
            val implication = z3Solver.mkImplies(z3Solver.mkAnd(loopCond, inv), wlp)
            val r = Invariant.checkForall(implication, allVars, z3Solver)
            /*if (!r._1) {
              println(inv)
              println(r)
              println()
            }*/
            r._1
          case None => false
        }
    })

    dp2 = (invGuess, validInvs) :: dp2
    val end = System.nanoTime()
    TOTAL_TIME_LOOP_INV += (end - start).toDouble / Utils.NANO

    // Invariant.removeWeakInvs(validInvs, allVars, z3Solver)
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
                              if (c1 * c2 > 0) acc3
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

  def varsToExprs(vars: Set[(String, TypeMirror)], z3Solver: Z3Solver): Set[Expr] = {
    vars.foldLeft(new HashSet[Expr])({
      case (acc, (name, typ)) =>
        val variable = if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
        else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
        else {
          assert(false)
          z3Solver.mkFalse()
        }
        acc + variable
    })
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

  // Return true iff. the assertion is valid
  def checkForall(assertion: BoolExpr, allVars: Set[Expr], z3Solver: Z3Solver): (Boolean, BoolExpr) = {
    val toCheck = {
      z3Solver.mkNot(
        z3Solver.mkForall(allVars.toArray, assertion)
      )
    }
    val res = z3Solver.checkSAT(toCheck)
    (!res, toCheck)
  }

  def getConjunction(invs: Iterable[BoolExpr], z3Solver: Z3Solver): BoolExpr = {
    if (invs.isEmpty) z3Solver.mkTrue()
    else if (invs.size == 1) invs.head
    else z3Solver.mkAnd(invs.toSeq: _*)
  }

  def printTime(): Unit = {
    Utils.printYellowString("Invariant inference's total time is: " + ("%.3f" format TOTAL_TIME_INV) + "s")
    Utils.printYellowString("Loop invariant inference's total time is: " + ("%.3f" format TOTAL_TIME_LOOP_INV) + "s")
  }

  // Cause more unnecessary z3 queries
  def removeFalseInvs(invs: Set[BoolExpr], allVars: Set[Expr], z3Solver: Z3Solver): Set[BoolExpr] = {
    // If an guessed invariant is equivalent to false (i.e. there does not exist a program state
    // that satisfies it), then any reasoning afterwards does not make sense
    val ret = invs.filter({
      inv =>
        val exists = z3Solver.mkExists(allVars.toArray, inv)
        z3Solver.checkSAT(exists)
    })
    Utils.printYellowString("[Remove false predicates] We reduced the # of predicates from " + invs.size + " to " + ret.size)
    ret
  }

  // Cause more unnecessary z3 queries
  def removeWeakInvs(invs: Set[BoolExpr], allVars: Set[Expr], z3Solver: Z3Solver): Set[BoolExpr] = {
    val NUM_OF_MAX_ITER = 50
    var ret = invs

    def printResult(): Unit = Utils.printYellowString("[Remove weak predicates] We reduced the # of predicates from " + invs.size + " to " + ret.size)

    var i = 0
    while (i < NUM_OF_MAX_ITER) {
      var toRemove: Option[BoolExpr] = None
      Utils.crossJoin(ret :: ret :: List[Set[BoolExpr]]()).find({
        pair =>
          val inv1 = pair.head
          val inv2 = pair.tail.head
          if (inv1.toString != inv2.toString) {
            val implication = z3Solver.mkImplies(inv1, inv2)
            val r = Invariant.checkForall(implication, allVars, z3Solver)
            if (r._1) {
              // println(r._1, r._2)
              toRemove = Some(inv2)
            }
            r._1
          }
          else false
      }) match {
        case Some(pair) =>
          val toRemove = pair.tail.head
          // println(ret.-(toRemove).size, ret.size, toRemove)
          ret = ret.-(toRemove)
        case None =>
          printResult()
          return ret
      }

      i = i + 1
    }
    printResult()
    ret
  }
}

case class InvGuess(loc: Block, graph: Graph[Block, DefaultEdge]) {
  override def equals(obj: Any): Boolean = {
    obj match {
      case guess: InvGuess =>
        val r1 = loc == guess.loc
        val r2 = GraphUtil.isSameGraph(graph, guess.graph)
        r1 && r2
      case _ => false
    }
  }
}

case class LoopInvGuess(loopHead: ConditionalBlock, loopCond: Expr, graph: Graph[Block, DefaultEdge]) {
  override def equals(obj: Any): Boolean = {
    obj match {
      case guess: LoopInvGuess =>
        val r1 = loopHead == guess.loopHead
        var r2 = loopCond.toString == guess.loopCond.toString
        val r3 = GraphUtil.isSameGraph(graph, guess.graph)
        r1 && r2 && r3
      case _ => false
    }
  }
}