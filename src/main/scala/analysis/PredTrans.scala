package analysis

import com.microsoft.z3.{BoolExpr, Expr}
import com.sun.source.tree._
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block._
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.javacutil.TreeUtils
import org.jgrapht.Graph
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import utils.GraphUtil

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
// Weakest precondition computation over a graph, instead of an AST
object PredTrans {
  val DEBUG_TRANS_EXPR = false
  val DEBUG = true
  val DEBUG_WLP_LOOP = false
  val DEBUG_WLP_PROG = false
  val DEBUG_WLP_BLOCK = DEBUG

  // Compute the weakest precondition of a given predicate over a given AST node (representing basic statements, instead of compound statements)
  def wlpBasic(node: Node, pred: BoolExpr, z3Solver: Z3Solver): BoolExpr = {
    if (node.getBlock.isInstanceOf[ExceptionBlock]) return pred

    val tree = node.getTree
    tree match {
      case variableTree: VariableTree =>
        val x = {
          val name = variableTree.getName.toString
          val typ = TreeUtils.typeOf(variableTree.getType)
          if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
          else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
          else {
            assert(false, tree.toString)
            z3Solver.mkFalse()
          }
        }
        val expr = transExpr(variableTree.getInitializer, z3Solver)
        pred.substitute(x, expr).asInstanceOf[BoolExpr]

      case assignmentTree: AssignmentTree => // Note that this is subtype of ExpressionTree
        val x = {
          val name = assignmentTree.getVariable.toString
          val typ = TreeUtils.typeOf(assignmentTree.getVariable)
          if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
          else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
          else {
            assert(false, tree.toString)
            z3Solver.mkFalse()
          }
        }
        val expr = transExpr(assignmentTree.getExpression, z3Solver)
        pred.substitute(x, expr).asInstanceOf[BoolExpr]

      case assertTree: AssertTree =>
        z3Solver.mkImplies(transExpr(assertTree.getCondition, z3Solver), pred)

      case expressionTree: ExpressionTree =>
        val shouldVisit = isTopLevelStmt(node)
        if (shouldVisit) return pred
        expressionTree.getKind match {
          case Tree.Kind.POSTFIX_DECREMENT => ??? // TODO
          case Tree.Kind.POSTFIX_INCREMENT => ??? // TODO
          case _ =>
            val typ = TreeUtils.typeOf(expressionTree)
            if (typ.getKind == TypeKind.BOOLEAN) {
              // Do nothing here. We should especially not consider boolean-typed expressions,
              // because they are conditionals and should be handled by getBranchCond.
              // z3Solver.mkAnd(transExpr(expressionTree, z3Solver), pred)
              pred
            }
            else if (typ.getKind == TypeKind.INT) {
              assert(false, tree.toString)
              z3Solver.mkFalse()
            } else {
              assert(false, tree.toString)
              z3Solver.mkFalse()
            }
        }

      case _ => pred
    }
  }

  def wlpBlock(curBlock: Block, pred: BoolExpr, z3Solver: Z3Solver): BoolExpr = {
    curBlock match {
      case reg: RegularBlock =>
        assert(reg != null && reg.getContents != null)
        getTopLevelStmts(reg).foldLeft(pred)(
          (accPred, node) => {
            if (node.getTree != null) {
              // Compute the weakest precondition of the instruction
              val newPred = PredTrans.wlpBasic(node, accPred, z3Solver)
              if (DEBUG_WLP_BLOCK) {
                println("WLP of statement " + node.getTree + " after predicate " + accPred + " is predicate " + newPred)
              }
              newPred
            }
            else accPred
          })
      case _ => pred
    }
  }

  // Compute the weakest precondition of the given predicate before the program starting at the given block
  def wlpProg(root: Block,
              graph: Graph[Block, DefaultEdge],
              pred: BoolExpr,
              z3Solver: Z3Solver,
              indent: Int = 0): BoolExpr = {
    if (DEBUG_WLP_PROG)
      println("\n\n\nInfer WLP before block " + root.getId + " in program " + graph.vertexSet().asScala.map(b => b.getId) + " for post-condition " + pred)

    val progNodes = graph.vertexSet().asScala

    // Check graph validity
    assert(graph.inDegreeOf(root) == 0)

    // SCC condensation graph
    val sccCds = GraphUtil.getSCCCondensation(graph)

    // Topologically sort SCCs
    val predicates = GraphUtil.reverseTopological(sccCds).foldLeft(new HashMap[Graph[Block, DefaultEdge], (BoolExpr, BoolExpr)])({
      (acc, scc) =>
        val hasCycle = GraphUtil.hasCycle(scc)
        val nodes = scc.vertexSet().asScala
        if (!hasCycle) assert(nodes.size == 1)

        if (DEBUG_WLP_PROG) {
          println("\nVisiting SCC: " + nodes.map(b => b.getId))
        }

        val outgoingEdges = sccCds.outgoingEdgesOf(scc).asScala
        val postPred: BoolExpr = {
          if (outgoingEdges.size == 1) {
            val nxtSCC = sccCds.getEdgeTarget(outgoingEdges.head)
            val nxtBlk = {
              val nxtNodes = nxtSCC.vertexSet().asScala
              val nxtBlks = nodes.foldLeft(new HashSet[Block])({
                (acc, node) =>
                  node match {
                    case b: SingleSuccessorBlock =>
                      if (nxtNodes.contains(b.getSuccessor)) acc + b.getSuccessor
                      else acc
                    case b: ConditionalBlock =>
                      if (nxtNodes.contains(b.getThenSuccessor)) acc + b.getThenSuccessor
                      else if (nxtNodes.contains(b.getElseSuccessor)) acc + b.getElseSuccessor
                      else acc
                  }
              })
              assert(nxtBlks.size == 1, nxtBlks.map(b => b.getId))
              assert(nxtNodes.contains(nxtBlks.head))
              nxtBlks.head
            }

            if (DEBUG_WLP_PROG) println("Next block is: " + nxtBlk)

            // If the next block is a conditional block, then the current block's post-condition
            // should be the pre-condition of that conditional block
            nxtBlk match {
              case nxtBlk: ConditionalBlock =>
                val cond = getBranchCond(nxtBlk, graph, z3Solver)
                val branches = sccCds.outgoingEdgesOf(nxtSCC).asScala
                val (thenSCC, elseSCC) = {
                  val emptyGraph = new DefaultDirectedGraph[Block, DefaultEdge](classOf[DefaultEdge])
                  val twoSCCs = branches.toList.map(edge => sccCds.getEdgeTarget(edge))
                  val headSCC = twoSCCs.head
                  val headIsThen = headSCC.vertexSet().contains(nxtBlk.getThenSuccessor)
                  val headIsElse = headSCC.vertexSet().contains(nxtBlk.getElseSuccessor)
                  if (branches.size == 2) {
                    if (headIsThen) (headSCC, twoSCCs(1))
                    else (twoSCCs(1), headSCC)
                  }
                  else if (branches.size == 1) {
                    if (headIsThen) (headSCC, emptyGraph)
                    else (emptyGraph, headSCC)
                  }
                  else {
                    assert(false)
                    (emptyGraph, emptyGraph)
                  }
                }

                if (DEBUG_WLP_PROG) {
                  println("Then SCC: " + thenSCC.vertexSet().asScala.map(b => b.getId))
                  println("Else SCC: " + elseSCC.vertexSet().asScala.map(b => b.getId))
                }

                (acc.get(thenSCC), acc.get(elseSCC)) match {
                  case (Some(thenPred), Some(elsePred)) =>
                    z3Solver.mkAnd(
                      z3Solver.mkImplies(cond, thenPred._1),
                      z3Solver.mkImplies(z3Solver.mkNot(cond), elsePred._1)
                    )
                  case (Some(thenPred), None) => z3Solver.mkImplies(cond, thenPred._1)
                  case (None, Some(elsePred)) => z3Solver.mkImplies(z3Solver.mkNot(cond), elsePred._1)
                  case _ => assert(false); z3Solver.mkFalse()
                }
              case nxtBlk: SingleSuccessorBlock =>
                acc.get(nxtSCC) match {
                  case Some(predicate) => predicate._1
                  case None => assert(false); z3Solver.mkFalse()
                }
              case _ => assert(false); z3Solver.mkFalse()
            }
          }
          else if (outgoingEdges.size == 2) {
            z3Solver.mkFalse() // We shall never read this value
          }
          else if (outgoingEdges.size > 2) {
            assert(false)
            z3Solver.mkFalse()
          }
          else {
            pred
          }
        }

        val prePred: BoolExpr = {
          if (hasCycle) {
            val loopHead = {
              val loopHeads = nodes.filter({
                case b: ConditionalBlock =>
                  val thenBlk = b.getThenSuccessor
                  val elseBlk = b.getElseSuccessor
                  (progNodes.contains(elseBlk) && progNodes.contains(thenBlk)) &&
                    (
                      (!nodes.contains(thenBlk) && nodes.contains(elseBlk)) ||
                        (!nodes.contains(elseBlk) && nodes.contains(thenBlk))
                      )
                case _ => false
              })
              assert(loopHeads.size == 1, loopHeads.map(b => b.getId))
              loopHeads.head
            }
            val loopInv = z3Solver.mkTrue() // TODO: Recursively invoke inferLocalInv?
            wlpLoop(scc, loopHead, loopInv, postPred, z3Solver)
          }
          else {
            wlpBlock(nodes.head, postPred, z3Solver)
          }
        }
        acc + (scc -> (prePred, postPred))
    })

    // Retrieve the result
    predicates.foreach({
      case (scc, (pre, post)) =>
        val nodes = scc.vertexSet().asScala

        if (DEBUG_WLP_PROG)
          println("\nResult of SCC :" + nodes.map(b => b.getId) + "\n  Pre-condition: " + pre + "\n  Post-condition: " + post)

        if (nodes.contains(root)) {
          predicates.get(scc) match {
            case Some(predicate) => return predicate._1
            case None =>
          }
        }
    })
    assert(false)
    z3Solver.mkFalse()
  }

  def wlpLoop(loopBody: Graph[Block, DefaultEdge],
              loopHead: Block,
              loopInv: BoolExpr,
              pred: BoolExpr,
              z3Solver: Z3Solver): BoolExpr = {
    assert(loopHead.isInstanceOf[ConditionalBlock], loopHead.toString)
    val loopBlks = loopBody.vertexSet().asScala
    if (DEBUG_WLP_LOOP) {
      println("\n\n\nInfer WLP before loop " + loopBlks.map(b => b.getId) + " with loop head at block " + loopHead.getId + " for post-condition " + pred)
    }

    // Get all assigned variables
    val assignedVars: Set[(String, TypeMirror)] = loopBlks.foldLeft(new HashSet[(String, TypeMirror)])({
      (acc, block) =>
        getTopLevelStmts(block).foldLeft(acc)({
          (acc2, node) =>
            node.getTree match {
              case variableTree: VariableTree =>
                acc2 + ((variableTree.getName.toString, TreeUtils.typeOf(variableTree.getType)))
              case assignmentTree: AssignmentTree =>
                acc2 + ((assignmentTree.getVariable.toString, TreeUtils.typeOf(assignmentTree.getVariable)))
              case _ => acc2
            }
        })
    })

    val loopCond = getBranchCond(loopHead, loopBody, z3Solver)

    if (DEBUG_WLP_LOOP) println("Assigned vars: " + assignedVars)
    if (DEBUG_WLP_LOOP) println("Loop condition: " + loopCond)

    // Find the weakest precondition when executing the loop body once
    val newGraph = GraphUtil.cloneGraph(loopBody)
    newGraph.vertexSet().asScala.foreach({
      // Break the loop by removing all back edges, i.e. edges ending up at loop head
      case loopBlk: SingleSuccessorBlock =>
        if (loopBlk.getSuccessor != null && loopBlk.getSuccessor.getId == loopHead.getId) {
          newGraph.removeEdge(loopBlk, loopBlk.getSuccessor)
        }
      case loopBlk: ConditionalBlock =>
        if (loopBlk.getThenSuccessor != null && loopBlk.getThenSuccessor.getId == loopHead.getId) {
          assert(false)
          newGraph.removeEdge(loopBlk, loopBlk.getThenSuccessor)
        }
        if (loopBlk.getElseSuccessor != null && loopBlk.getElseSuccessor.getId == loopHead.getId) {
          assert(false)
          newGraph.removeEdge(loopBlk, loopBlk.getElseSuccessor)
        }
      case _ =>
    })

    val loopBodyWlp = wlpProg(loopHead, newGraph, loopInv, z3Solver)
    val body: Expr = {
      val body = z3Solver.mkAnd(
        z3Solver.mkImplies(z3Solver.mkAnd(loopCond, loopInv), loopBodyWlp),
        z3Solver.mkImplies(z3Solver.mkAnd(z3Solver.mkNot(loopCond), loopInv), pred)
      )
      if (assignedVars.nonEmpty) {
        z3Solver.mkForall(
          assignedVars.toArray.map({
            case (name, typ) =>
              if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
              else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
              else {
                assert(false, typ)
                z3Solver.mkFalse()
              }
          }),
          body
        )
      }
      else {
        body
      }
    }
    val ret = z3Solver.mkAnd(loopInv, body)
    if (DEBUG_WLP_LOOP) println("WLP before the loop: " + ret)
    ret
  }

  // Find the branching condition. The branching block must only have one predecessor
  // Please make sure that results of function invocation are assigned to variables (instead of being directly used),
  // because function invocation will always lead to the generation of an exception handling block
  def getBranchCond(block: Block, graph: Graph[Block, DefaultEdge], z3Solver: Z3Solver): BoolExpr = {
    assert(block.isInstanceOf[ConditionalBlock])
    val incomingEdges = graph.incomingEdgesOf(block).asScala
    assert(incomingEdges.size == 1)
    graph.getEdgeSource(incomingEdges.head) match {
      case reg: RegularBlock =>
        reg.getContents.asScala.last.getTree match {
          case expTree: ExpressionTree => transExpr(expTree, z3Solver).asInstanceOf[BoolExpr]
          case x@_ => assert(false, x); z3Solver.mkTrue()
        }
      /*case exp: ExceptionBlock =>
        val incomingEdges2 = graph.incomingEdgesOf(exp).asScala
        assert(incomingEdges2.size == 1)
        graph.getEdgeSource(incomingEdges2.head) match {
          case reg2: RegularBlock =>
            reg2.getContents.asScala.last.getTree match {
              case expTree: ExpressionTree => transExpr(expTree, z3Solver).asInstanceOf[BoolExpr]
              case x@_ => assert(false, x); z3Solver.mkTrue()
            }
          case x@_ => assert(false, x); z3Solver.mkTrue()
        }*/
      case x@_ => assert(false, x.getId+"=>"+block.getId); z3Solver.mkTrue()
    }
  }

  // If there is no parent tree of this expression tree succeeding it in the same basic block
  def isTopLevelStmt(node: Node): Boolean = {
    val block = node.getBlock.asInstanceOf[RegularBlock].getContents.asScala
    val idx = block.indexOf(node)
    !block.zipWithIndex.exists({
      case (n, i) =>
        if (i > idx) {
          val transOps = n.getTransitiveOperands
          transOps.asScala.exists(op => op == node)
        }
        else false
    })
  }

  def getTopLevelStmts(block: Block): List[Node] = {
    block match {
      case reg: RegularBlock => reg.getContents.asScala.filter({
        node => isTopLevelStmt(node)
      }).toList
      case _ => List[Node]() // We don't consider non-regular blocks as being possible to contain top level statements
    }
  }

  // Transform an expression tree into a Z3 expression
  def transExpr(expressionTree: ExpressionTree, z3Solver: Z3Solver): Expr = {
    val typ = TreeUtils.typeOf(expressionTree)
    val isInt = typ.getKind == TypeKind.INT
    val isBool = typ.getKind == TypeKind.BOOLEAN
    val defaultVal = {
      if (isInt) z3Solver.mkIntVal(0)
      else if (isBool) z3Solver.mkFalse()
      else {
        assert(false, expressionTree.toString + ": " + expressionTree.getKind)
        z3Solver.mkFalse()
      }
    }

    if (DEBUG_TRANS_EXPR) println(expressionTree, typ)

    expressionTree match {
      case identifierTree: IdentifierTree =>
        // We only consider boolean or integer variables
        if (isInt) z3Solver.mkIntVar(identifierTree.toString)
        else if (isBool) z3Solver.mkBoolVar(identifierTree.toString)
        else {
          assert(false, expressionTree.toString)
          defaultVal
        }

      case literalTree: LiteralTree =>
        // We only consider boolean or integer literals
        literalTree.getKind match {
          case Tree.Kind.BOOLEAN_LITERAL => if (literalTree.toString == "true") z3Solver.mkTrue() else z3Solver.mkFalse()
          case Tree.Kind.INT_LITERAL => z3Solver.mkIntVal(literalTree.toString.toInt)
          case _ => assert(false, expressionTree.toString); z3Solver.mkTrue()
        }

      case methodInvocationTree: MethodInvocationTree =>
        // We only consider boolean typed method invocation
        if (isBool) z3Solver.mkRandBoolVar()
        else {
          assert(false, expressionTree.toString)
          defaultVal
        }

      case binaryTree: BinaryTree =>
        val left = transExpr(binaryTree.getLeftOperand, z3Solver)
        val right = transExpr(binaryTree.getRightOperand, z3Solver)
        binaryTree.getKind match {
          case Tree.Kind.CONDITIONAL_AND => z3Solver.mkAnd(left, right)
          case Tree.Kind.CONDITIONAL_OR => z3Solver.mkOr(left, right)
          case Tree.Kind.DIVIDE => z3Solver.mkDiv(left, right)
          case Tree.Kind.EQUAL_TO => z3Solver.mkEq(left, right)
          case Tree.Kind.GREATER_THAN => z3Solver.mkGt(left, right)
          case Tree.Kind.GREATER_THAN_EQUAL => z3Solver.mkGe(left, right)
          case Tree.Kind.LESS_THAN => z3Solver.mkLt(left, right)
          case Tree.Kind.LESS_THAN_EQUAL => z3Solver.mkLe(left, right)
          case Tree.Kind.MINUS => z3Solver.mkSub(left, right)
          case Tree.Kind.MULTIPLY => z3Solver.mkMul(left, right)
          case Tree.Kind.NOT_EQUAL_TO => z3Solver.mkNe(left, right)
          case Tree.Kind.PLUS => z3Solver.mkAdd(left, right)
          case _ => assert(false, expressionTree.toString); defaultVal
        }

      case unaryTree: UnaryTree =>
        unaryTree.getKind match {
          case Tree.Kind.UNARY_PLUS => transExpr(unaryTree.getExpression, z3Solver)
          case Tree.Kind.UNARY_MINUS => z3Solver.mkSub(z3Solver.mkIntVal(0), transExpr(unaryTree.getExpression, z3Solver))
          case Tree.Kind.LOGICAL_COMPLEMENT => z3Solver.mkNot(z3Solver.mkBoolVar(unaryTree.getExpression.toString))
          case _ => assert(false, expressionTree.toString); defaultVal
        }

      // case arrayAccessTree: ArrayAccessTree =>

      case parenthesizedTree: ParenthesizedTree => transExpr(parenthesizedTree.getExpression, z3Solver)

      case _ => defaultVal
    }
  }
}
