package analysis

import org.checkerframework.dataflow.cfg.block.{Block, RegularBlock}
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import utils.GraphUtil

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG = true

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(block: RegularBlock, graph: DefaultDirectedGraph[Block, DefaultEdge], indent: Int = 0): Unit = {
    val indentStr = " "*indent
    if (DEBUG) println("\n\n\n"+indentStr+"---Infer invariant right after block: " + block.getId)
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val newGraph = graph.clone().asInstanceOf[DefaultDirectedGraph[Block, DefaultEdge]]
    newGraph.removeEdge(block, block.getSuccessor)
    val newSimCycles = GraphUtil.getAllSimpleCycles(newGraph)

    simCycles.foreach(simCycle => {
      if (DEBUG) println("\n"+indentStr+"Simple cycle: " + simCycle.map(b => b.getId))
      val idx = simCycle.indexOf(block)
      if (idx != -1) {
        var j = if (idx == 0) simCycle.size - 1 else idx - 1
        while (j != idx) { // Backwards traversal
          if (DEBUG) println(indentStr+"  curBlock: " + simCycle(j).getId)
          val innerLoops = newSimCycles.filter(il => il.contains(simCycle(j)))
          if (innerLoops.nonEmpty) {
            val commonNodes: Set[List[Block]] = innerLoops.map(il => il.intersect(simCycle))
            val maxLoop = commonNodes.max(Ordering[Int].on[List[Block]](l => l.size))

            val idx = maxLoop.map(b => simCycle.indexOf(b))
            val maxIdx = idx.max(Ordering[Int].on[Int](n => if (n > j) j + (simCycle.size - n) else j - n))
            if (DEBUG) {
              println(indentStr+"  Max loop: " + maxLoop.map(b => b.getId))
              println(indentStr+"  Farthest block away from j: " + simCycle(maxIdx).getId)
            }
            inferLocalInv(simCycle(maxIdx).asInstanceOf[RegularBlock], newGraph, indent+2)
            j = if (maxIdx == 0) simCycle.size - 1 else maxIdx - 1 // Skip the intersecting part
          } else {
            j = if (j == 0) simCycle.size - 1 else j - 1
          }
        }
      } // Otherwise, the given block is not in the current loop
    })
    if (DEBUG) println(indentStr+"---Invariant inferred right after block: " + block.getId)
  }

  // Infer inductive global invariants (which are very demanding)
  def inferGlobalInv(graph: DefaultDirectedGraph[Block, DefaultEdge]): Unit = {

  }
}
