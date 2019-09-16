package utils

import java.io.IOException
import java.util

import org.checkerframework.dataflow.cfg.block._
import org.checkerframework.dataflow.cfg.{ControlFlowGraph, DOTCFGVisualizer}
import org.jgrapht.Graph
import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.alg.cycle.{CycleDetector, JohnsonSimpleCycles}
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.jgrapht.traverse.TopologicalOrderIterator

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object GraphUtil {
  def cfgToJgraphtGraph(cfg: ControlFlowGraph): DefaultDirectedGraph[Block, DefaultEdge] = {
    val graph = new DefaultDirectedGraph[Block, DefaultEdge](classOf[DefaultEdge])
    val nodes = cfg.getAllBlocks.asScala.toSet
    nodes.foreach(node => graph.addVertex(node))
    nodes.foreach({
      case reg: RegularBlock => graph.addEdge(reg, reg.getRegularSuccessor)
      // println(reg.getId, reg.getRegularSuccessor.getId)
      case cond: ConditionalBlock =>
        graph.addEdge(cond, cond.getThenSuccessor)
        graph.addEdge(cond, cond.getElseSuccessor)
      // println(cond.getId, cond.getElseSuccessor.getId, cond.getThenSuccessor.getId)
      case special: SpecialBlock =>
        graph.addVertex(special)
        if (special.getSuccessor != null) {
          graph.addVertex(special.getSuccessor)
          graph.addEdge(special, special.getSuccessor)
        }
      case exception: ExceptionBlock =>
        exception.getExceptionalSuccessors.asScala.foreach({
          case (typ, blocks) => blocks.asScala.foreach(block => graph.addEdge(exception, block))
        })
        if (exception.getSuccessor != null) {
          graph.addVertex(exception.getSuccessor)
          graph.addEdge(exception, exception.getSuccessor)
        }
      case _ => assert(false)
    })
    graph
  }

  def getAllSimpleCycles[V, E](graph: Graph[V, E]): Set[List[V]] = {
    val jAlg = new JohnsonSimpleCycles(graph)
    val cycles = jAlg.findSimpleCycles()
    cycles.asScala.toSet.map({ cycle: java.util.List[V] => cycle.asScala.toList })
  }

  def getSCCs[V, E](graph: Graph[V, E]): Set[Graph[V, E]] = {
    val scAlg: StrongConnectivityAlgorithm[V, E] = new KosarajuStrongConnectivityInspector[V, E](graph)
    val stronglyConnectedSubgraphs = scAlg.getStronglyConnectedComponents
    stronglyConnectedSubgraphs.asScala.toSet
  }

  def getSCCCondensation[V, E](graph: Graph[V, E]): Graph[Graph[V, E], DefaultEdge] = {
    val scAlg: StrongConnectivityAlgorithm[V, E] = new KosarajuStrongConnectivityInspector[V, E](graph)
    scAlg.getCondensation
  }

  def printGraph(graph: Graph[Block, DefaultEdge]): Unit = {
    graph.vertexSet().asScala.foreach(b => println(b.getId, b.toString))
    graph.edgeSet().asScala.foreach(edge => println(graph.getEdgeSource(edge).getId + " => " + graph.getEdgeTarget(edge).getId))
  }

  def printCFGtoPDF(cfg: ControlFlowGraph, outputDir: String): Unit = {
    val args = new util.HashMap[String, AnyRef]
    args.put("outdir", outputDir)
    args.put("checkerName", "")

    val viz = new DOTCFGVisualizer
    viz.init(args)
    val res = viz.visualize(cfg, cfg.getEntryBlock, null)
    viz.shutdown()
    val file = res.get("dotFileName").asInstanceOf[String]
    try {
      val command = "dot -Tpdf " + file + " -o " + file + ".pdf"
      val child = Runtime.getRuntime.exec(command)
      child.waitFor
    } catch {
      case e@(_: InterruptedException | _: IOException) =>
        e.printStackTrace()
        System.exit(1)
    }
  }

  // A copy of the original graph, where nodes are shallow copied and edges are deep copied
  def cloneGraph(graph: Graph[Block, DefaultEdge]): Graph[Block, DefaultEdge] = {
    val newGraph = new DefaultDirectedGraph[Block, DefaultEdge](classOf[DefaultEdge])

    val nodes: Set[Block] = graph.vertexSet().asScala.toSet
    val edges: Set[DefaultEdge] = graph.edgeSet().asScala.toSet
    nodes.foreach(node => newGraph.addVertex(node))
    edges.foreach(edge => newGraph.addEdge(graph.getEdgeSource(edge), graph.getEdgeTarget(edge)))
    newGraph
  }

  def hasCycle[V, E](graph: Graph[V, E]): Boolean = new CycleDetector(graph).detectCycles()

  def reverseTopological[V, E](graph: Graph[V, E]): List[V] = {
    var res = List[V]()
    val it = new TopologicalOrderIterator(graph)
    while (it.hasNext) {
      res = it.next() :: res
    }
    res
  }
}

case class MyCFG(cfg: ControlFlowGraph) {
  val graph: DefaultDirectedGraph[Block, DefaultEdge] = GraphUtil.cfgToJgraphtGraph(cfg)
  val simCycles: Set[List[Block]] = GraphUtil.getAllSimpleCycles(graph)
}

// References
// - https://stackoverflow.com/questions/546655/finding-all-cycles-in-a-directed-graph
// - https://code.google.com/archive/p/niographs/
// - https://networkx.github.io/documentation/latest/reference/algorithms/generated/networkx.algorithms.cycles.simple_cycles.html
// - https://en.wikipedia.org/wiki/Cycle_(graph_theory)