package analysis

import boundchecker.Vars
import com.microsoft.z3.{BoolExpr, Expr, IntExpr}
import com.sun.source.tree.MethodTree
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.{Block, ConditionalBlock, SingleSuccessorBlock}
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
  val DEBUG_LOCAL_INV = false
  val DEBUG_GEN_NEW_INV = false

  var TOTAL_TIME: Double = 0

  var dp = List[(InvGuess, Set[BoolExpr])]()

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(loc: Block,
                    graph: Graph[Block, DefaultEdge],
                    allVars: Set[Expr],
                    pred: BoolExpr, // The predicate abstracting the context under which invariants need to be inferred
                    z3Solver: Z3Solver,
                    indent: Int = 0): Set[BoolExpr] = {
    val start = System.nanoTime()
    val invGuess = InvGuess(loc, graph)
    dp.foreach({
      case (invGuessp, inv) =>
        if (invGuessp.equals(invGuess)) {
          // println("!!!!!!!!!!!!!!!")
          return inv
        }
    })

    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer invariant right after block " + loc.getId + " started:")
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val invs = guessLocalInv(allVars, z3Solver)
    if (DEBUG_GEN_NEW_INV) println("# of vars: " + allVars.size + "\n# of invs: " + invs.size)
    val validInvs = invs.filter({
      inv =>
        // The inferred invariant must not contradict the context, i.e. exist state(s) s.t. state|=pred and state|=inv
        // val validity = z3Solver.mkAnd(pred, inv)
        // z3Solver.checkSAT(validity)
        true
    }).filter({
      inv =>
        if (DEBUG_LOCAL_INV) println(indentStr + "Verify the validity of invariant " + inv)
        // If for all simple cycles, if the guessed local invariant is valid right after the end of the given block,
        // then it will be valid again next time reaching the end of the given block,
        // then the guessed local invariant is valid
        simCycles.forall(simCycle => {
          if (DEBUG_LOCAL_INV) println("\n" + indentStr + "Simple cycle: " + simCycle.map(b => b.getId))
          var acc = inv
          val idx = simCycle.indexOf(loc)
          if (idx != -1) {
            // Remove the edge in the current simple cycle that starts from the given block, preventing visiting
            // the given block again
            val nxtBlock = if (idx == simCycle.size - 1) simCycle.head else simCycle(idx + 1)
            val newGraph = GraphUtil.cloneGraph(graph)
            newGraph.vertexSet().asScala.foreach(
              {
                b =>
                  if (b.getId == loc.getId) {
                    b match {
                      case b: SingleSuccessorBlock =>
                        if (b.getSuccessor.getId == nxtBlock.getId)
                          newGraph.removeEdge(b, b.getSuccessor)
                        else
                          assert(false, b.toString)
                      case b: ConditionalBlock =>
                        if (b.getThenSuccessor.getId == nxtBlock.getId)
                          newGraph.removeEdge(b, b.getThenSuccessor)
                        else if (b.getElseSuccessor.getId == nxtBlock.getId)
                          newGraph.removeEdge(b, b.getElseSuccessor)
                        else
                          assert(false, b.toString)
                      case _ => assert(false, b.toString)
                    }
                  }
              }
            )

            // Backwards traversal
            var j = idx
            do {
              val curBlock = simCycle(j)
              if (DEBUG_LOCAL_INV) println(indentStr + "->curBlock " + curBlock.getId)

              // Find out the SCC containing the current block
              val sccs = GraphUtil.getSCCs(newGraph).filter(graph => graph.vertexSet().asScala.contains(curBlock))
              assert(sccs.size == 1)

              val theSCC = sccs.head
              // If the SCC contains a loop
              if (GraphUtil.hasCycle(theSCC)) {
                // The current block must be the loop head, i.e. one of its successor must be outside the loop
                val loopBody = theSCC.vertexSet()
                curBlock match {
                  case b: ConditionalBlock =>
                    val thenBlk = b.getThenSuccessor
                    val elseBlk = b.getElseSuccessor
                    assert(thenBlk != null && elseBlk != null)
                    assert(
                      (!loopBody.contains(thenBlk) && loopBody.contains(elseBlk)) ||
                        (!loopBody.contains(elseBlk) && loopBody.contains(thenBlk))
                    )
                  case _ => assert(false)
                }

                // Find local invariants for the (semantic) inner loop in the new graph under the context of ??? s.t.
                // if the invariant is valid right after the loop head, then it will be valid again upon next visit
                val loopInvs = {
                  // Recursive invocation of this procedure will lead to verifying exponential # of invariants
                  // This is unsound because `true` is not verified to be a valid loop invariant
                  // Additionally, `true` might be too weak to prove the guessed invariant is indeed valid!
                  // List(z3Solver.mkTrue())
                  inferLocalInv(
                    curBlock,
                    theSCC,
                    allVars,
                    z3Solver.mkTrue(),
                    z3Solver,
                    indent + 2
                  )
                }

                // Infer the weakest precondition before entering the inner loop
                if (loopInvs.isEmpty) {
                  // Stop exploration because we cannot find loop invariants and hence cannot compute wlp!
                  val res = new HashSet[BoolExpr]()
                  dp = (InvGuess(loc, graph), res) :: dp
                  return res
                }
                else {
                  // If any of the inferred inner loop's invariant may work, then we are happy :)
                  val loopPreds = loopInvs.map(loopInv => PredTrans.wlpLoop(theSCC, curBlock, loopInv, acc, z3Solver))
                  acc = {
                    if (loopPreds.size <= 1) loopPreds.head
                    else z3Solver.mkOr(loopPreds.toSeq: _*)
                  }
                  if (DEBUG_LOCAL_INV) {
                    loopPreds.foreach(loopPred => println(indentStr + "  Loop wlp: " + loopPred))
                  }
                }

                /*if (inv.toString == "(< (+ i (* (- 1) n)) 0)" || inv.toString == "(< (+ (* (- 1) n) i) 0)") {
                  loopInvs.foreach(inv => println(inv))
                }*/

                // Make the inner loop acyclic by removing the edge starting from the current block
                val toRemove = {
                  val thenBlk = curBlock.asInstanceOf[ConditionalBlock].getThenSuccessor
                  val elseBlk = curBlock.asInstanceOf[ConditionalBlock].getElseSuccessor
                  if (loopBody.contains(thenBlk)) thenBlk
                  else if (loopBody.contains(elseBlk)) elseBlk
                  else {
                    assert(false)
                    curBlock
                  }
                }
                newGraph.removeEdge(curBlock, toRemove)
              }

              // Process the current block
              // We should also collect path constraints here!
              curBlock match {
                case condBlk: ConditionalBlock =>
                  val nxtBlk = if (j == simCycle.size - 1) simCycle.head else simCycle(j + 1)
                  val branching = PredTrans.getBranchCond(condBlk, newGraph, z3Solver)
                  val cond = if (condBlk.getThenSuccessor == nxtBlk) branching else z3Solver.mkNot(branching)
                  acc = z3Solver.mkImplies(cond, acc)
                case _ => acc = PredTrans.wlpBlock(curBlock, acc, z3Solver)
              }
              if (DEBUG_LOCAL_INV) {
                println(indentStr + "<-curBlock " + curBlock.getId + " wlp: " + acc + "\n")
              }

              j = if (j == 0) simCycle.size - 1 else j - 1
            } while (j != idx)
          }
          else {
            // Otherwise, we do nothing because the given block is not in the current loop --- since this block
            // will not be visited a second time via this simple cycle, the guessed local invariant is vacuously valid
          }

          val implication = z3Solver.mkImplies(inv, acc) // TODO: Which direction?
          val res = Invariant.checkForall(implication, allVars, z3Solver)
          if (DEBUG_LOCAL_INV) {
            println(indentStr + "  " + "Check the validity of inv " + inv.toString + " via " + res._2)
            println(indentStr + "  " + "Z3 result: " + res._1 + "\n")
          }
          res._1
        })
    })
    if (DEBUG_LOCAL_INV) {
      println(indentStr + "---Infer invariant right after block " + loc.getId + " finishes.")
      println(indentStr + "---Valid invariants are: " + validInvs.foldLeft("\n")((acc, b) => acc + b + "\n"))
    }

    dp = (InvGuess(loc, graph), validInvs) :: dp
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

  def guessLocalInv(vars: Set[Expr], z3Solver: Z3Solver): Set[BoolExpr] = {
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
                                acc3 + (le.toString -> le) + (lt.toString -> lt)
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

  def guessGlobInv(allVars: Set[(String, TypeMirror)], z3Solver: Z3Solver): Set[BoolExpr] = {
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

  def guessBounds(vars: Vars, z3Solver: Z3Solver): Set[BoolExpr] = {
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

  def getConjunction(invs: Set[BoolExpr], z3Solver: Z3Solver): Expr = {
    if (invs.isEmpty) z3Solver.mkTrue()
    else if (invs.size == 1) invs.head
    else z3Solver.mkAnd(invs.toSeq: _*)
  }

  def printTime(): Unit = Utils.printRedString("Local invariant inference's total time is: " + ("%.3f" format TOTAL_TIME) + "s")
}

case class InvGuess(loc: Block, graph: Graph[Block, DefaultEdge]) {
  override def equals(obj: Any): Boolean = {
    obj match {
      case res: InvGuess =>
        val r1 = loc == res.loc
        val r2 = GraphUtil.isSameGraph(graph, res.graph)
        r1 && r2
      case _ => false
    }
  }
}