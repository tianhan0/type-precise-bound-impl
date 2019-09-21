package utils

import java.io.{File, IOException}
import java.util

import analysis.PredTrans
import com.sun.source.tree.{AssignmentTree, BinaryTree, ExpressionTree, IdentifierTree, ParenthesizedTree, Tree, UnaryTree, VariableTree}
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block._
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.dataflow.cfg.{ControlFlowGraph, DOTCFGVisualizer}
import org.checkerframework.javacutil.TreeUtils
import org.jgrapht.Graph
import org.jgrapht.alg.connectivity.KosarajuStrongConnectivityInspector
import org.jgrapht.alg.cycle.{CycleDetector, JohnsonSimpleCycles}
import org.jgrapht.alg.interfaces.StrongConnectivityAlgorithm
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import org.jgrapht.io.{ComponentNameProvider, DOTExporter}
import org.jgrapht.traverse.TopologicalOrderIterator

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

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

  def printGraphtoPDF(graph: Graph[Block, DefaultEdge], fileName: String): Unit = {
    val vertexIdProvider = new ComponentNameProvider[Block]() {
      override def getName(block: Block): String = block.getId.toString
    }
    val vertexLabelProvider = new ComponentNameProvider[Block]() {
      override def getName(block: Block): String = {
        block.getId.toString + " [" + block.getType.toString + "]\n" + PredTrans.getTopLevelStmts(block).foldLeft("")((acc, s) => acc + s + "\n")
      }
    }
    val dotExp = new DOTExporter[Block, DefaultEdge](vertexIdProvider, vertexLabelProvider, null)
    val dotFile = fileName+".dot"
    val pdfFile = fileName+".pdf"
    try {
      dotExp.exportGraph(graph, new File(dotFile))
      val command = "dot -Tpdf " + dotFile + " -o " + pdfFile
      val child = Runtime.getRuntime.exec(command)
      child.waitFor
    } catch {
      case e@(_: InterruptedException | _: IOException) =>
        e.printStackTrace()
        System.exit(1)
    }
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

  def isSameGraph(g1: Graph[Block, DefaultEdge], g2: Graph[Block, DefaultEdge]): Boolean = {
    val nodes1 = g1.vertexSet().asScala
    val nodes2 = g2.vertexSet().asScala
    if (nodes1.union(nodes2) == nodes1 && nodes2.union(nodes1) == nodes2) {
      val edges1 = g1.edgeSet().asScala
      val edges2 = g2.edgeSet().asScala
      false
    }
    else false
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

  def getAllVars(graph: Graph[Block, DefaultEdge]): Set[(String, TypeMirror)] = {
    def getVars(tree: Tree): Set[(String, TypeMirror)] = {
      if (tree == null) return new HashSet[(String, TypeMirror)]
      tree match {
        case expressionTree: ExpressionTree =>
          expressionTree match {
            case identifierTree: IdentifierTree =>
              val typ = TreeUtils.typeOf(expressionTree)
              val isInt = typ.getKind == TypeKind.INT
              val isBool = typ.getKind == TypeKind.BOOLEAN
              // We only consider boolean or integer variables
              if (isInt) HashSet[(String, TypeMirror)]((identifierTree.toString, typ))
              else if (isBool) HashSet[(String, TypeMirror)]((identifierTree.toString, typ))
              else {
                // assert(false, expressionTree.toString + ": " + typ)
                new HashSet[(String, TypeMirror)]
              }

            case binaryTree: BinaryTree =>
              binaryTree.getKind match {
                case Tree.Kind.CONDITIONAL_AND | Tree.Kind.CONDITIONAL_OR | Tree.Kind.DIVIDE | Tree.Kind.EQUAL_TO | Tree.Kind.GREATER_THAN | Tree.Kind.GREATER_THAN_EQUAL | Tree.Kind.LESS_THAN | Tree.Kind.LESS_THAN_EQUAL | Tree.Kind.MINUS | Tree.Kind.MULTIPLY | Tree.Kind.NOT_EQUAL_TO | Tree.Kind.PLUS => getVars(binaryTree.getLeftOperand) ++ getVars(binaryTree.getRightOperand)
                case _ => assert(false, expressionTree.toString); new HashSet[(String, TypeMirror)]
              }

            case unaryTree: UnaryTree =>
              unaryTree.getKind match {
                case Tree.Kind.UNARY_PLUS | Tree.Kind.UNARY_MINUS | Tree.Kind.LOGICAL_COMPLEMENT => getVars(unaryTree.getExpression)
                case _ => assert(false, expressionTree.toString); new HashSet[(String, TypeMirror)]
              }

            case parenthesizedTree: ParenthesizedTree => getVars(parenthesizedTree.getExpression)

            case assignmentTree: AssignmentTree =>
              getVars(assignmentTree.getExpression) + ((assignmentTree.getVariable.toString, TreeUtils.typeOf(assignmentTree.getVariable)))

            case _ => new HashSet[(String, TypeMirror)]
          }
        case variableTree: VariableTree =>
          val initializer = variableTree.getInitializer
          getVars(initializer) + ((variableTree.getName.toString, TreeUtils.typeOf(variableTree.getType)))
        case _ => new HashSet[(String, TypeMirror)]
      }
    }

    graph.vertexSet().asScala.flatMap({
      case reg: RegularBlock => reg.getContents.asScala
      case _ => List[Node]()
    }).foldLeft(new HashSet[(String, TypeMirror)])({
      (acc, node) =>
        if (node != null) acc ++ getVars(node.getTree)
        else acc
    })
  }
}

case class MyCFG(cfg: ControlFlowGraph) {
  val graph: DefaultDirectedGraph[Block, DefaultEdge] = GraphUtil.cfgToJgraphtGraph(cfg)
  // val simCycles: Set[List[Block]] = GraphUtil.getAllSimpleCycles(graph)
  val allVars: Set[(String, TypeMirror)] = GraphUtil.getAllVars(graph)
}

// References
// - https://stackoverflow.com/questions/546655/finding-all-cycles-in-a-directed-graph
// - https://code.google.com/archive/p/niographs/
// - https://networkx.github.io/documentation/latest/reference/algorithms/generated/networkx.algorithms.cycles.simple_cycles.html
// - https://en.wikipedia.org/wiki/Cycle_(graph_theory)