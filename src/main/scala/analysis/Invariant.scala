package analysis

import com.microsoft.z3.BoolExpr
import com.sun.source.tree._
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.{Block, ConditionalBlock, RegularBlock, SingleSuccessorBlock}
import org.checkerframework.javacutil.TreeUtils
import org.jgrapht.Graph
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import utils.GraphUtil
import org.checkerframework.dataflow.cfg.node.Node

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
object Invariant {
  val DEBUG_LOCAL_INV = false
  val DEBUG_PRED_TRANS = true

  // Return the predicate s.t. if it is valid right after the end of the given block, then it will be valid again next time reaching the end of the given block
  def inferLocalInv(loc: Block,
                    graph: Graph[Block, DefaultEdge],
                    pred: BoolExpr, // The predicate abstracting the context under which invariants need to be inferred
                    z3Solver: Z3Solver,
                    indent: Int = 0): Set[BoolExpr] = {
    val indentStr = " " * indent
    if (DEBUG_LOCAL_INV) println("\n\n\n" + indentStr + "---Infer inference right after block " + loc.getId + " started:")
    val simCycles = GraphUtil.getAllSimpleCycles(graph)

    val invs = genNewInv(graph, z3Solver)
    val validInvs = invs.filter({
      inv =>
        // The inferred invariant must not contradict the context, i.e. exist state(s) s.t. state|=pred and state|=inv
        val validity = z3Solver.mkAnd(pred, inv)
        z3Solver.push()
        z3Solver.mkAssert(validity)
        val res = z3Solver.checkSAT
        z3Solver.pop()
        res
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
                  if (DEBUG_PRED_TRANS) println("Loop wlp: " + initLoopInvWlp)
                  acc = loopInvs.tail.foldLeft(initLoopInvWlp)({
                    (acc, loopInv) =>
                      val loopInvWlp = PredTrans.wlpLoop(theSCC, curBlock, loopInv, wlpAfterLoop, z3Solver)
                      if (DEBUG_PRED_TRANS) println("Loop wlp: " + loopInvWlp)
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
              if (DEBUG_PRED_TRANS) println("Block " + curBlock.getId + " wlp: " + acc + "\n")

              j = if (j == 0) simCycle.size - 1 else j - 1
            } while (j != idx)
          }
          else {
            // Otherwise, we do nothing because the given block is not in the current loop --- since this block
            // will not be visited a second time via this simple cycle, the guessed local invariant is vacuously valid
          }
          val implication = z3Solver.mkImplies(inv, acc) // TODO: Which direction?
          z3Solver.push()
          val toCheck = z3Solver.mkForall(
            getAllVars(graph).toArray.map({
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
          z3Solver.mkAssert(z3Solver.mkNot(toCheck))
          if (DEBUG_PRED_TRANS) println("Check the validity of inv " + inv.toString + " via " + implication + "\n")
          val res = z3Solver.checkSAT
          z3Solver.pop()
          !res
        })
    })
    if (DEBUG_LOCAL_INV) println(indentStr + "---Invariant inference right after block " + loc.getId + " finishes.")
    validInvs
  }

  // Infer inductive global invariants (which are very demanding)
  def inferGlobalInv(graph: DefaultDirectedGraph[Block, DefaultEdge]): Unit = {

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

  def genNewInv(graph: Graph[Block, DefaultEdge], z3Solver: Z3Solver): Set[BoolExpr] = {
    var ret = new HashSet[BoolExpr]()
    ret += z3Solver.mkGt(z3Solver.mkIntVar("R"), z3Solver.mkIntVar("i")) // z3Solver.mkTrue()
    ret
  }
}
