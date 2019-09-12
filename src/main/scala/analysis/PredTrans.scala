package analysis

import com.microsoft.z3.{BoolExpr, Expr}
import com.sun.source.tree._
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.{Block, ConditionalBlock, RegularBlock, SingleSuccessorBlock}
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.javacutil.TreeUtils
import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import utils.GraphUtil

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
// Weakest precondition computation over a graph, instead of an AST
object PredTrans {
  val DEBUG_TRANS_EXPR = false

  // Compute the weakest precondition of a given predicate over a given AST node (representing basic statements, instead of compound statements)
  def wlpBasic(node: Node, pred: BoolExpr, z3Solver: Z3Solver): BoolExpr = {
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

      case assignmentTree: AssignmentTree =>
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
          case Tree.Kind.POSTFIX_DECREMENT => z3Solver.mkTrue() // TODO
          case Tree.Kind.POSTFIX_INCREMENT => z3Solver.mkTrue() // TODO
          case _ =>
            val typ = TreeUtils.typeOf(expressionTree)
            if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkAnd(transExpr(expressionTree, z3Solver), pred)
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

  // Compute the weakest precondition starting from the given block
  def wlpProg(start: Block,
              end: Block,
              graph: Graph[Block, DefaultEdge],
              pred: BoolExpr,
              z3Solver: Z3Solver,
              indent: Int = 0): BoolExpr = {
    ???
  }

  def wlpLoop(loop: Graph[Block, DefaultEdge],
              start: Block,
              end: Block,
              loopInv: BoolExpr,
              pred: BoolExpr,
              z3Solver: Z3Solver): BoolExpr = {
    assert(end.isInstanceOf[RegularBlock])
    val loopBlks = loop.vertexSet().asScala

    // Get all assigned variables
    val assignedVars: Set[(String, TypeMirror)] = loopBlks.foldLeft(new HashSet[(String, TypeMirror)])({
      (acc, block) =>
        getTopLevelStmts(block).foldLeft(acc)({
          (acc2, node) =>
            node.getTree match {
              case variableTree: VariableTree =>
                acc2 + ((variableTree.getName.toString, TreeUtils.typeOf(variableTree.getInitializer)))
              case assignmentTree: AssignmentTree =>
                acc2 + ((assignmentTree.getVariable.toString, TreeUtils.typeOf(assignmentTree.getVariable)))
              case _ => acc2
            }
        })
    })

    // Find the loop condition
    val loopCond = end match {
      case reg: RegularBlock =>
        reg.getContents.asScala.last.getTree match {
          case expTree: ExpressionTree => transExpr(expTree, z3Solver)
          case x@_ => assert(false, x); z3Solver.mkTrue()
        }
      case _ => assert(false, end); z3Solver.mkTrue()
    }

    // println(assignedVars, loopCond)

    // Find the weakest precondition when executing the loop body once
    val newGraph = GraphUtil.cloneGraph(loop)
    val nodes = newGraph.vertexSet()
    newGraph.vertexSet().asScala.foreach(
      // Break the loop by removing back edges
      b => {
        if (b.getId == end.getId) {
          b match {
            case reg: RegularBlock =>
              loopBlks.foreach({
                case loopBlk: SingleSuccessorBlock => if (loopBlk.getSuccessor == b) newGraph.removeEdge(loopBlk, b)
                case loopBlk: ConditionalBlock =>
                  if (loopBlk.getThenSuccessor == b) newGraph.removeEdge(loopBlk, b)
                  if (loopBlk.getElseSuccessor == b) newGraph.removeEdge(loopBlk, b)
                case _ =>
              })
            case _ =>
          }
        }
      }
    )

    val loopBodyWlp = wlpProg(start, end, newGraph, loopInv, z3Solver)

    val ret = {
      z3Solver.mkAnd(
        loopInv,
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
          z3Solver.mkAnd(
            z3Solver.mkImplies(z3Solver.mkAnd(loopCond, loopInv), loopBodyWlp),
            z3Solver.mkImplies(z3Solver.mkAnd(z3Solver.mkNot(loopCond)), pred)
          )
        )
      )
    }
    // println(ret)
    ret
  }

  // If there is no parent tree of this expression tree succeeding it in the same basic block
  def isTopLevelStmt(node: Node): Boolean = {
    val block = node.getBlock.asInstanceOf[RegularBlock].getContents.asScala
    val idx = block.indexOf(node)
    !block.zipWithIndex.exists({
      case (n, i) =>
        if (i > idx) {
          val transOps = n.getTransitiveOperands
          transOps.asScala.exists(op => op == n)
        }
        else false
    })
  }

  def getTopLevelStmts(block: Block): List[Node] = {
    block match {
      case reg: RegularBlock => reg.getContents.asScala.filter(node => isTopLevelStmt(node)).toList
      case _ => List[Node]()
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
        assert(false, expressionTree.toString)
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
          case _ => assert(false, expressionTree.toString); defaultVal
        }

      // case arrayAccessTree: ArrayAccessTree =>

      case parenthesizedTree: ParenthesizedTree => transExpr(parenthesizedTree.getExpression, z3Solver)

      case _ => defaultVal
    }
  }
}
