package analysis

import com.microsoft.z3.BoolExpr
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.{Block, ConditionalBlock, SingleSuccessorBlock}
import utils.{GraphUtil, MyCFG}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG = false
  val DEBUG_LOCAL_INV = DEBUG
  val DEBUG_PRED_TRANS = DEBUG
  val DEBUG_GEN_NEW_INV = false

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(loc: Block,
                    myCFG: MyCFG, // graph: Graph[Block, DefaultEdge],
                    pred: BoolExpr, // The predicate abstracting the context under which invariants need to be inferred
                    z3Solver: Z3Solver,
                    indent: Int = 0): Set[BoolExpr] = {
    val graph = myCFG.graph
    val allVars = myCFG.allVars

    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer inference right after block " + loc.getId + " started:")
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val invs = genNewLocalInv(allVars, z3Solver)
    if (DEBUG_GEN_NEW_INV) println("# of vars: " + allVars.size + "\n# of invs: " + invs.size)
    val validInvs = invs.filter({
      inv =>
        // The inferred invariant must not contradict the context, i.e. exist state(s) s.t. state|=pred and state|=inv
        val validity = z3Solver.mkAnd(pred, inv)
        z3Solver.checkSAT(validity)
    }).filter({
      inv =>
        if (DEBUG_PRED_TRANS) println(indentStr + "Verify the validity of invariant " + inv)
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
                  List(z3Solver.mkTrue())
                  /*inferLocalInv(
                    curBlock,
                    theSCC,
                    z3Solver.mkTrue(),
                    z3Solver,
                    indent + 2
                  )*/
                }

                // Infer the weakest precondition before entering the inner loop
                if (loopInvs.isEmpty) {
                  // Stop exploration because we cannot find loop invariants and hence cannot compute wlp!
                  return new HashSet[BoolExpr]()
                }
                else {
                  // If any of the inferred inner loop's invariant may work, then we are happy :)
                  val loopPreds = loopInvs.map(loopInv => PredTrans.wlpLoop(theSCC, curBlock, loopInv, acc, z3Solver))
                  acc = z3Solver.mkOr(loopPreds: _*)
                  if (DEBUG_PRED_TRANS) {
                    loopPreds.foreach(loopPred => println(indentStr + "  Loop wlp: " + loopPred))
                    /*z3Solver.push()
                    z3Solver.mkAssert(acc)
                    val res = z3Solver.checkSAT
                    z3Solver.pop()
                    assert(res, acc)*/
                  }
                }

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
              acc = PredTrans.wlpBlock(curBlock, acc, z3Solver)
              if (DEBUG_PRED_TRANS) {
                println(indentStr + "<-curBlock " + curBlock.getId + " wlp: " + acc + "\n")
                /*z3Solver.push()
                z3Solver.mkAssert(acc)
                val res = z3Solver.checkSAT
                z3Solver.pop()
                assert(res, acc)*/
              }

              j = if (j == 0) simCycle.size - 1 else j - 1
            } while (j != idx)
          }
          else {
            // Otherwise, we do nothing because the given block is not in the current loop --- since this block
            // will not be visited a second time via this simple cycle, the guessed local invariant is vacuously valid
          }
          val implication = z3Solver.mkImplies(inv, acc) // TODO: Which direction?
          val toCheck = {
            /*z3Solver.mkNot(
              z3Solver.mkForall(
                allVars.toArray.map({
                  case (name, typ) =>
                    if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
                    else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
                    else {
                      assert(false)
                      z3Solver.mkFalse()
                    }
                }),
                implication
              )
            )*/
            implication
          }
          val res = z3Solver.checkSAT(toCheck)
          if (DEBUG_PRED_TRANS)
            println(indentStr + "  Check the validity of inv " + inv.toString + " via\n" + toCheck + "\nZ3 result: " + res + "\n")
          res
        })
    })
    if (DEBUG_LOCAL_INV) println(indentStr + "---Invariant inference right after block " + loc.getId + " finishes.")
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

  def genNewLocalInv(allVars: Set[(String, TypeMirror)], z3Solver: Z3Solver): Set[BoolExpr] = {
    val coeff = HashSet[Int](-1, 1)
    val constants = {
      val pos = HashSet[Int](0, 1)
      pos.map(n => -n) ++ pos
    }

    allVars.zipWithIndex.foldLeft(new HashMap[String, BoolExpr])({
      case (acc, ((name1, typ1), idx1)) =>
        allVars.zipWithIndex.foldLeft(acc)({
          case (accp, ((name2, typ2), idx2)) =>
            if (idx2 > idx1) {
              (getTyp(typ1), getTyp(typ2)) match {
                case (TypeKind.INT, TypeKind.INT) =>
                  val var1 = z3Solver.mkIntVar(name1)
                  val var2 = z3Solver.mkIntVar(name2)

                  coeff.foldLeft(accp)({
                    (acc1, c1) =>
                      coeff.foldLeft(acc1)({
                        (acc2, c2) =>
                          constants.foldLeft(acc2)({
                            (acc3, c3) =>
                              val expr = z3Solver.mkLe(
                                z3Solver.mkAdd(
                                  z3Solver.mkMul(z3Solver.mkIntVal(c1), var1),
                                  z3Solver.mkMul(z3Solver.mkIntVal(c2), var2)
                                ),
                                z3Solver.mkIntVal(c3)
                              )
                              acc3 + (expr.toString -> expr)
                          })
                      })
                  })
                case _ => accp
              }
            }
            else accp
        })
    }).values.toSet + z3Solver.mkTrue()
    /*HashSet[BoolExpr](
      z3Solver.mkLe(
        z3Solver.mkAdd(
          z3Solver.mkMul(z3Solver.mkIntVal(1), z3Solver.mkIntVar("R")),
          z3Solver.mkMul(z3Solver.mkIntVal(-1), z3Solver.mkIntVar("i"))
        ),
        z3Solver.mkIntVal(0))
    )*/
  }

  def genNewGlobInv(allVars: Set[(String, TypeMirror)], z3Solver: Z3Solver): Set[BoolExpr] = {
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

  def rmDupInvs(invs: Set[BoolExpr], z3Solver: Z3Solver): Set[BoolExpr] = {
    invs.foldLeft(new HashSet[BoolExpr])({
      (acc, inv) =>
        val canBeImplied = acc.exists(p => {
          val implication = z3Solver.mkImplies(p, inv)
          z3Solver.checkSAT(implication)
        })
        if (canBeImplied) acc
        else acc + inv
    })
  }
}