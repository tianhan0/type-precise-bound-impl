import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.alg.cycle.JohnsonSimpleCycles
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.scalatest.{FlatSpec, Matchers}

import collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
class GraphTest extends FlatSpec with Matchers {
  val directedGraph = new DefaultDirectedGraph[String, DefaultEdge](classOf[DefaultEdge])
  directedGraph.addVertex("a")
  directedGraph.addVertex("b")
  directedGraph.addVertex("c")
  directedGraph.addVertex("d")
  directedGraph.addVertex("e")
  directedGraph.addVertex("f")
  directedGraph.addVertex("g")
  directedGraph.addVertex("h")
  directedGraph.addVertex("i")
  directedGraph.addEdge("a", "b")
  directedGraph.addEdge("b", "d")
  directedGraph.addEdge("d", "c")
  directedGraph.addEdge("c", "a")
  directedGraph.addEdge("e", "d")
  directedGraph.addEdge("e", "f")
  directedGraph.addEdge("f", "g")
  directedGraph.addEdge("g", "e")
  directedGraph.addEdge("h", "e")
  directedGraph.addEdge("i", "h")


  // computes all the strongly connected components of the directed graph// computes all the strongly connected components of the directed graph
  val scAlg: StrongConnectivityAlgorithm[String, DefaultEdge] = new KosarajuStrongConnectivityInspector[String, DefaultEdge](directedGraph)
  val stronglyConnectedSubgraphs = scAlg.getStronglyConnectedComponents

  // prints the strongly connected components
  println("Strongly connected components:")
  stronglyConnectedSubgraphs.asScala.foreach(scc => println(scc))

  val jAlg = new JohnsonSimpleCycles(directedGraph)
  println("All simple cycles")
  jAlg.findSimpleCycles().asScala.foreach(cycle => println(cycle))
}
