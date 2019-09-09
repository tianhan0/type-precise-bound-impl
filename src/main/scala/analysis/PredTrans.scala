package analysis

import com.microsoft.z3.{BoolExpr, Expr}
import com.sun.source.tree._
import javax.lang.model.`type`.TypeKind
import org.checkerframework.javacutil.TreeUtils

/**
  * @author Tianhan Lu
  */
object PredTrans {
  val DEBUG_TRANS_EXPR = false

  // Compute the weakest precondition of a given predicate over a given AST node (representing basic statements, instead of compound statements)
  def wlp(tree: Tree, pred: BoolExpr, z3Solver: Z3Solver): BoolExpr = {
    tree match {
      case variableTree: VariableTree =>
        val x = {
          val name = variableTree.getName.toString
          val typ = TreeUtils.typeOf(variableTree.getType)
          if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
          else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
          else z3Solver.mkBoolVar(name)
        }
        val expr = transExpr(variableTree.getInitializer, z3Solver)
        pred.substitute(x, expr).asInstanceOf[BoolExpr]
        
      case assignmentTree: AssignmentTree =>
        val x = {
          val name = assignmentTree.getVariable.toString
          val typ = TreeUtils.typeOf(assignmentTree.getVariable)
          if (typ.getKind == TypeKind.INT) z3Solver.mkIntVar(name)
          else if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkBoolVar(name)
          else z3Solver.mkBoolVar(name)
        }
        val expr = transExpr(assignmentTree.getExpression, z3Solver)
        pred.substitute(x, expr).asInstanceOf[BoolExpr]
        
      case assertTree: AssertTree =>
        z3Solver.mkAnd(transExpr(assertTree.getCondition, z3Solver), pred)
        
      case expressionTree: ExpressionTree =>
        expressionTree.getKind match {
          case Tree.Kind.POSTFIX_DECREMENT => // TODO
          case Tree.Kind.POSTFIX_INCREMENT => // TODO
          case _ =>
            val typ = TreeUtils.typeOf(expressionTree)
            if (typ.getKind == TypeKind.BOOLEAN) z3Solver.mkAnd(transExpr(expressionTree, z3Solver), pred)
            else if (typ.getKind == TypeKind.INT) z3Solver.mkIntVal(0)
            else z3Solver.mkIntVal(0)
        }
        pred
        
      case _ => pred
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
      else z3Solver.mkFalse()
    }

    if (DEBUG_TRANS_EXPR) println(expressionTree, typ)

    expressionTree match {
      case identifierTree: IdentifierTree =>
        // We only consider boolean or integer variables
        if (isInt) z3Solver.mkIntVar(identifierTree.toString)
        else if (isBool) z3Solver.mkBoolVar(identifierTree.toString)
        else defaultVal

      case literalTree: LiteralTree =>
        // We only consider boolean or integer literals
        literalTree.getKind match {
          case Tree.Kind.BOOLEAN_LITERAL => if (literalTree.toString == "true") z3Solver.mkTrue() else z3Solver.mkFalse()
          case Tree.Kind.INT_LITERAL => z3Solver.mkIntVal(literalTree.toString.toInt)
          case _ => z3Solver.mkTrue()
        }

      case methodInvocationTree: MethodInvocationTree =>
        // We only consider boolean typed method invocation
        if (isBool) z3Solver.mkRandBoolVar()
        else defaultVal

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
          case _ => defaultVal
        }

      case unaryTree: UnaryTree =>
        unaryTree.getKind match {
          case Tree.Kind.UNARY_PLUS => transExpr(unaryTree.getExpression, z3Solver)
          case Tree.Kind.UNARY_MINUS => z3Solver.mkSub(z3Solver.mkIntVal(0), transExpr(unaryTree.getExpression, z3Solver))
          case _ => defaultVal
        }

      // case arrayAccessTree: ArrayAccessTree =>

      case parenthesizedTree: ParenthesizedTree => transExpr(parenthesizedTree.getExpression, z3Solver)

      case _ => defaultVal
    }
  }
}
