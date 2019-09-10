package analysis

import com.microsoft.z3.BoolExpr
import org.checkerframework.dataflow.cfg.block.{Block, RegularBlock}
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import utils.GraphUtil

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG_LOCAL_INV = false

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(block: RegularBlock,
                    graph: DefaultDirectedGraph[Block, DefaultEdge],
                    ctxPred: BoolExpr, // The predicate abstracting the context under which invariants need to be inferred
                    z3Solver: Z3Solver,
                    indent: Int = 0): Set[BoolExpr] = {
    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer invariant right after block: " + block.getId)
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val newGraph = graph.clone().asInstanceOf[DefaultDirectedGraph[Block, DefaultEdge]]
    newGraph.removeEdge(block, block.getSuccessor)
    val newSimCycles = GraphUtil.getAllSimpleCycles(newGraph)

    val invs = genNewInv(z3Solver)
    val validInvs = invs.filter({
      inv =>
        // The inferred invariant must not contradict the context
        val validity = z3Solver.mkAnd(ctxPred, inv)
        z3Solver.mkAssert(validity)
        z3Solver.checkSAT // TODO: Clear Z3 up?
    }).filter({
      inv =>
        val wlpInv = simCycles.foldLeft(inv)((acc, simCycle) => {
          if (DEBUG_LOCAL_INV) println("\n" + indentStr + "Simple cycle: " + simCycle.map(b => b.getId))
          var newInv = acc
          val idx = simCycle.indexOf(block)
          if (idx != -1) {
            // Backwards traversal
            var j = if (idx == 0) simCycle.size - 1 else idx - 1
            while (j != idx) {
              val curBlock = simCycle(j)
              if (DEBUG_LOCAL_INV) println(indentStr + "  curBlock: " + curBlock.getId)

              val innerLoops = newSimCycles.filter(il => il.contains(curBlock))
              if (innerLoops.nonEmpty) {
                val commonNodes: Set[List[Block]] = innerLoops.map(il => il.intersect(simCycle))
                val maxLoop = commonNodes.max(Ordering[Int].on[List[Block]](l => l.size))

                val idx = maxLoop.map(b => simCycle.indexOf(b))
                // Find the block that is farthest away from the current block
                val maxIdx = idx.max(Ordering[Int].on[Int](n => if (n > j) j + (simCycle.size - n) else j - n))

                if (DEBUG_LOCAL_INV) {
                  println(indentStr + "  Max loop: " + maxLoop.map(b => b.getId))
                  println(indentStr + "  Farthest block away from j: " + simCycle(maxIdx).getId)
                }

                // Find loop invariants for (semantic) inner loops
                val loopInvs = inferLocalInv(
                  simCycle(maxIdx).asInstanceOf[RegularBlock],
                  newGraph,
                  newInv,
                  z3Solver,
                  indent + 2
                )

                // Infer the weakest precondition of the loop
                if (loopInvs.isEmpty) {
                  // Stop exploration because we cannot find loop invariants and hence cannot compute wlp!
                  return new HashSet[BoolExpr]()
                }
                else {
                  // Find out the MSCC starting at curBlock and ending up at block j, i.e. the whole loop
                  val loopBody = ???

                  val initLoopInvWlp = PredTrans.wlpLoop(loopBody, loopInvs.head, newInv, z3Solver)
                  newInv = loopInvs.tail.foldLeft(initLoopInvWlp)({
                    (acc, loopInv) =>
                      // newInv is never modified inside this loop
                      val loopInvWlp = PredTrans.wlpLoop(loopBody, loopInv, newInv, z3Solver)
                      // If any of the inferred inner loop's invariant may work, then we are happy :)
                      z3Solver.mkOr(acc, loopInvWlp)
                  })
                }

                // Skip the intersecting part
                j = if (maxIdx == 0) simCycle.size - 1 else maxIdx - 1
              }
              else {
                // Process current block if it is not in any loop
                newInv = curBlock match {
                  case reg: RegularBlock =>
                    assert(reg != null && reg.getContents != null)
                    reg.getContents.asScala.foldLeft(newInv)(
                      (accPred, node) => {
                        if (node.getTree != null) {
                          // Infer the weakest precondition of the block
                          val newPred = PredTrans.wlpBasic(node, accPred, z3Solver)
                          // println(newPred)
                          newPred
                        }
                        else accPred
                      })
                  case _ => newInv
                }
                j = if (j == 0) simCycle.size - 1 else j - 1
              }
            }
          }
          else {
            // Otherwise, the given block is not in the current loop
          }
          newInv
        })
        val implication = z3Solver.mkImplies(wlpInv, inv)
        z3Solver.mkAssert(implication)
        z3Solver.checkSAT // TODO: Clear Z3 up?
    })
    if (DEBUG_LOCAL_INV) println(indentStr + "---Invariant inferred right after block: " + block.getId)
    validInvs
  }

  // Infer inductive global invariants (which are very demanding)
  def inferGlobalInv(graph: DefaultDirectedGraph[Block, DefaultEdge]): Unit = {

  }

  def genNewInv(z3Solver: Z3Solver): Set[BoolExpr] = {
    new HashSet[BoolExpr]()
  }
}
