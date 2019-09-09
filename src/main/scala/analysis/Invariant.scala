package analysis

import org.checkerframework.dataflow.cfg.block.{Block, RegularBlock}
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import utils.GraphUtil

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG_LOCAL_INV = false

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(block: RegularBlock,
                    graph: DefaultDirectedGraph[Block, DefaultEdge],
                    z3Solver: Z3Solver,
                    indent: Int = 0): Unit = {
    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer invariant right after block: " + block.getId)
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val newGraph = graph.clone().asInstanceOf[DefaultDirectedGraph[Block, DefaultEdge]]
    newGraph.removeEdge(block, block.getSuccessor)
    val newSimCycles = GraphUtil.getAllSimpleCycles(newGraph)

    simCycles.foreach(simCycle => {
      if (DEBUG_LOCAL_INV) println("\n" + indentStr + "Simple cycle: " + simCycle.map(b => b.getId))
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

            inferLocalInv(simCycle(maxIdx).asInstanceOf[RegularBlock], newGraph, z3Solver, indent + 2)

            j = if (maxIdx == 0) simCycle.size - 1 else maxIdx - 1 // Skip the intersecting part
          } else {
            // Process current block if it is not in any loop
            curBlock match {
              case reg: RegularBlock =>
                assert(reg != null && reg.getContents != null)
                reg.getContents.asScala.foldLeft(z3Solver.mkTrue())(
                  (accPred, node) => {
                    if (node.getTree != null) {
                      val newPred = PredTrans.wlp(node.getTree, accPred, z3Solver)
                      // println(newPred)
                      newPred
                    }
                    else accPred
                  })
              case _ =>
            }
            j = if (j == 0) simCycle.size - 1 else j - 1
          }
        }
      }
      // Otherwise, the given block is not in the current loop
    })
    if (DEBUG_LOCAL_INV) println(indentStr + "---Invariant inferred right after block: " + block.getId)
  }

  // Infer inductive global invariants (which are very demanding)
  def inferGlobalInv(graph: DefaultDirectedGraph[Block, DefaultEdge]): Unit = {

  }
}
