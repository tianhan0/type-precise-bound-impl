package analysis

import com.microsoft.z3.BoolExpr
import org.checkerframework.dataflow.cfg.block.{Block, ConditionalBlock, SingleSuccessorBlock}
import org.jgrapht.Graph
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import utils.GraphUtil

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG_LOCAL_INV = true

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(loc: Block,
                    graph: Graph[Block, DefaultEdge],
                    pred: BoolExpr, // The predicate abstracting the context under which invariants need to be inferred
                    z3Solver: Z3Solver,
                    indent: Int = 0): Set[BoolExpr] = {
    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer inference right after block " + loc.getId + " started:")
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val invs = genNewInv(z3Solver)
    val validInvs = invs.filter({
      inv =>
        // The inferred invariant must not contradict the context
        val validity = z3Solver.mkImplies(pred, inv)
        z3Solver.mkAssert(validity)
        z3Solver.checkSAT // TODO: Clear Z3 up?
    }).filter({
      inv =>
        // If for all simple cycles, if the guessed local invariant is valid right after the end of the given block,
        // then it will be valid again next time reaching the end of the given block,
        // then the guessed local invariant is valid
        simCycles.forall(simCycle => {
          if (DEBUG_LOCAL_INV) println("\n" + indentStr + "Simple cycle: " + simCycle.map(b => b.getId))
          var acc = pred
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
              if (DEBUG_LOCAL_INV) println(indentStr + "  curBlock: " + curBlock.getId)

              // Find out the SCC containing the current block
              val sccs = GraphUtil.getSCCs(newGraph).filter(graph => graph.vertexSet().asScala.contains(curBlock))
              assert(sccs.size == 1)

              val theSCC = sccs.head
              // If the SCC contains a loop
              if (GraphUtil.hasCycle(theSCC)) {
                // if (DEBUG_LOCAL_INV)  GraphUtil.getAllSimpleCycles(theSCC).foreach(loop => println(indentStr + "" + loop.map(b => b.getId).toString()))

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
                val loopInvs = inferLocalInv(
                  curBlock,
                  theSCC,
                  z3Solver.mkTrue(),
                  z3Solver,
                  indent + 2
                )

                // Infer the weakest precondition before entering the inner loop
                if (loopInvs.isEmpty) {
                  // Stop exploration because we cannot find loop invariants and hence cannot compute wlp!
                  return new HashSet[BoolExpr]()
                }
                else {
                  val wlpAfterLoop = acc
                  val initLoopInvWlp = PredTrans.wlpLoop(theSCC, curBlock, loopInvs.head, wlpAfterLoop, z3Solver)
                  acc = loopInvs.tail.foldLeft(initLoopInvWlp)({
                    (acc, loopInv) =>
                      val loopInvWlp = PredTrans.wlpLoop(theSCC, curBlock, loopInv, wlpAfterLoop, z3Solver)
                      // If any of the inferred inner loop's invariant may work, then we are happy :)
                      z3Solver.mkOr(acc, loopInvWlp)
                  })
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

              j = if (j == 0) simCycle.size - 1 else j - 1
            } while (j != idx)
          }
          else {
            // Otherwise, we do nothing because the given block is not in the current loop --- since this block
            // will not be visited a second time via this simple cycle, the guessed local invariant is vacuously valid
          }
          val implication = z3Solver.mkImplies(acc, inv)
          z3Solver.mkAssert(implication)
          z3Solver.checkSAT // TODO: Clear Z3 up?
        })
    })
    if (DEBUG_LOCAL_INV) println(indentStr + "---Invariant inference right after block " + loc.getId + " finishes.")
    validInvs
  }

  // Infer inductive global invariants (which are very demanding)
  def inferGlobalInv(graph: DefaultDirectedGraph[Block, DefaultEdge]): Unit = {

  }

  def genNewInv(z3Solver: Z3Solver): Set[BoolExpr] = {
    var ret = new HashSet[BoolExpr]()
    ret += z3Solver.mkTrue()
    ret
  }
}
