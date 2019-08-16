import scala.collection.immutable.HashMap

/**
  * @author Tianhan Lu
  */

class Stmt

class Pred

case class Node(stmts: List[Stmt])

case class Mscc(head: Node, body: Set[Node])

case class Edge(from: Node, to: Node, pred: Pred)

case class Graph(entry: Node, nodes: Set[Node], edges: Set[Edge])

abstract class AlgSkeleton(program: Graph, trans: Node=>Pred=>Pred) {
  def algorithm(): Map[Mscc, Set[Pred]] = {
    getLoops(Mscc(program.entry, program.nodes)).foldLeft(new HashMap[Mscc, Set[Pred]]) {
      (acc, loop) => acc + (loop -> getLoopInv(loop))
    }
  }

  def getLoopInv(loop: Mscc): Set[Pred] = {

  }

  /**
    *
    * @param mscc
    * @return a set of maximal strongly connected components inside the given mscc
    */
  def decompose(mscc: Mscc): Set[Mscc]

  /**
    *
    * @param mscc
    * @return If there exists a path s.t. starts and ends at a same node inside mscc and all nodes on the path are inside mscc
    */
  def containsLoop(mscc: Mscc): Boolean

  /**
    *
    * @param mscc
    * @return An numeration of all paths s.t. starts from mscc.head and ends up at mscc.head, where each node on the path is a top level MSCC in mscc
    */
  def getPathProg(mscc: Mscc): Set[List[Mscc]] = {
    val msccs = decompose(mscc)
    ???
  }

  /**
    *
    * @param mscc
    * @return Top level MSCCs in mscc s.t. each contains at least one loop
    */
  def getLoops(mscc: Mscc): Set[Mscc] = decompose(mscc).filter(m => containsLoop(m))
}
