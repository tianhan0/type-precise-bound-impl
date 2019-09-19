package analysis

import utils.Utils
import com.microsoft.z3._

import scala.collection.immutable.HashMap


/**
  * @author Tianhan Lu
  */
class Z3Solver {
  val ctx: Context = new Context
  var vars: HashMap[String, Expr] = new HashMap[String, Expr]
  val DEBUG: Boolean = false

  val solver: Solver = {
    // cxt.setPrintMode(Z3_PRINT_LOW_LEVEL)
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 20000)
    solver.setParameters(params)
    // assert: for all x, len(x) is non-negative (use pattern?)
    solver
  }

  def mkPattern(expr: Expr*): Pattern = ctx.mkPattern(expr: _*)

  /*def mkLenFun(sort: Sort): FuncDecl = {
    mkUnintFun("len", Array(sort), ctx.getIntSort)
  }

  def applyLenFun(expr: Expr): Expr = mkLenFun(expr.getSort).apply(expr)*/

  def checkSAT: Boolean = {
    val start = System.nanoTime()
    val res = interpretSolverOutput(solver.check)
    val end = System.nanoTime()
    Z3Solver.TOTAL_TIME += (end - start).toDouble / Utils.NANO
    Z3Solver.TOTAL_QUERY += 1
    if (DEBUG) Z3Solver.printTime()
    res
  }

  def checkSAT(asts: AST*): Boolean = {
    push()
    asts.foreach(ast => mkAssert(ast))
    val res = checkSAT
    pop()
    res
  }

  /**
    *
    * @param n: We want n models
    * @param expr: The expression of interest
    * @return n models s.t. each model evaluates expr to a different value
    *         Note: This method has side effects!
    */
  def findNModels(n: Int, expr: Expr): List[Model] = {
    var list = List[Model]()
    while (list.size < n) {
      checkSAT
      val model = solver.getModel
      list = model :: list
      mkAssert(mkNe(expr, model.eval(expr, false)))
    }
    list
  }

  def checkSATWithAssumptions(assumes: List[String]): Boolean =
    interpretSolverOutput(solver.check(assumes.map(assume => ctx.mkBoolConst(assume)): _*))

  def push(): Unit = solver.push()

  def pop(): Unit = solver.pop()

  def getUNSATCore: String = sys.error("Unimp")

  private def interpretSolverOutput(status: Status): Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new Exception("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  /*
  def getNatVar(k: String): AST = {
    val ast = getVar(k)
    mkAssert(mkGe(ast, mkIntVal(0)))
    ast
  }*/

  def mkNone(sort: Sort): Expr = ctx.mkConst("none", sort)

  def mkTrue(): BoolExpr = ctx.mkTrue()

  def mkFalse(): BoolExpr = ctx.mkFalse()

  def mkIntVal(i: Int): IntNum = ctx.mkInt(i)

  def mkBoolVal(b: Boolean): BoolExpr = ctx.mkBool(b)

  def mkRange(lb: ArithExpr, e: ArithExpr, ub: ArithExpr): BoolExpr = ctx.mkAnd(ctx.mkLe(e, ub), ctx.mkLe(lb, e))

  def mkAssert(asts: AST*): Unit = {
    asts.foreach(ast => solver.add(ast.asInstanceOf[BoolExpr]))
  }

  def mkNot(o: AST): BoolExpr = ctx.mkNot(o.asInstanceOf[BoolExpr])

  def mkEq(lhs: AST, rhs: AST): BoolExpr = ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])

  def mkNe(lhs: AST, rhs: AST): BoolExpr = ctx.mkNot(ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr]))

  def mkGt(lhs: AST, rhs: AST): BoolExpr = ctx.mkGt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkLt(lhs: AST, rhs: AST): BoolExpr = ctx.mkLt(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkGe(lhs: AST, rhs: AST): BoolExpr = ctx.mkGe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkLe(lhs: AST, rhs: AST): BoolExpr = ctx.mkLe(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkAdd(lhs: AST, rhs: AST): ArithExpr = ctx.mkAdd(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkAdd(ast: AST*): ArithExpr = {
    if (ast.isEmpty) mkIntVal(0)
    else ctx.mkAdd(ast.map(a => a.asInstanceOf[ArithExpr]): _*)
  }

  def mkSub(lhs: AST, rhs: AST): ArithExpr = ctx.mkSub(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkMul(lhs: AST, rhs: AST): ArithExpr = ctx.mkMul(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkDiv(lhs: AST, rhs: AST): ArithExpr = ctx.mkDiv(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  def mkRem(lhs: AST, rhs: AST): IntExpr = ctx.mkMod(lhs.asInstanceOf[IntExpr], rhs.asInstanceOf[IntExpr])

  def mkImplies(lhs: AST, rhs: AST): BoolExpr = ctx.mkImplies(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkAnd(lhs: AST, rhs: AST): BoolExpr = ctx.mkAnd(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkAnd(ast: AST*): BoolExpr = {
    if (ast.isEmpty) assert(false)
    ctx.mkAnd(ast.map(a => a.asInstanceOf[BoolExpr]): _*)
  }

  def mkOr(lhs: AST, rhs: AST): BoolExpr = ctx.mkOr(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkOr(ast: AST*): BoolExpr = {
    if (ast.isEmpty) assert(false)
    ctx.mkOr(ast.map(a => a.asInstanceOf[BoolExpr]): _*)
  }

  def mkXor(lhs: AST, rhs: AST): BoolExpr = ctx.mkXor(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  def mkIntVar(s: String): IntExpr = {
    vars.get(s) match {
      case Some(v) => v.asInstanceOf[IntExpr]
      case None =>
        val expr = ctx.mkIntConst(s)
        vars += (s -> expr)
        expr
    }
  }

  def mkRandIntVar(): IntExpr = {
    var name = Utils.genRandStr()
    while (vars.contains(name)) {
      name = Utils.genRandStr()
    }
    mkIntVar(name)
  }

  def mkBoolVar(s: String): BoolExpr = {
    vars.get(s) match {
      case Some(v) => v.asInstanceOf[BoolExpr]
      case None =>
        val expr = ctx.mkBoolConst(s)
        vars += (s -> expr)
        expr
    }
  }

  def mkRandBoolVar(): BoolExpr = {
    var name = Utils.genRandStr()
    while (vars.contains(name)) {
      name = Utils.genRandStr()
    }
    mkBoolVar(name)
  }

  def mkVar(s: String, sort: Sort): Expr = {
    vars.get(s) match {
      case Some(v) => v
      case None =>
        val expr = ctx.mkConst(s, sort)
        vars += (s -> expr)
        expr
    }
  }

  def mkRandVar(sort: Sort): Expr = {
    var name = Utils.genRandStr()
    while (vars.contains(name)) {
      name = Utils.genRandStr()
    }
    mkVar(name, sort)
  }

  def mkUnintFun(s: String, in: Array[Sort], out: Sort): FuncDecl = ctx.mkFuncDecl(s, in, out)

  def mkExists(boundVars: Array[Expr], expr: Expr): Quantifier = ctx.mkExists(boundVars, expr, 1, null, null, null, null)

  def mkExists(boundVars: Array[Expr], expr: Expr, patterns: Array[Pattern]): Quantifier = ctx.mkExists(boundVars, expr, 1, patterns, null, null, null)

  def mkForall(boundVars: Array[Expr], expr: Expr): Quantifier = ctx.mkForall(boundVars, expr, 1, null, null, null, null)

  def mkForall(boundVars: Array[Expr], expr: Expr, patterns: Array[Pattern]): Quantifier = ctx.mkForall(boundVars, expr, 1, patterns, null, null, null)

  /**
    *
    * @param obj the objective to optimize for
    * @param max maximize or minimize
    */
  def optimize(obj: Expr, max: Boolean = true): Integer = {
    val opt = ctx.mkOptimize
    val objExpr = if (max) opt.MkMaximize(obj) else opt.MkMinimize(obj)
    opt.Add(solver.getAssertions: _*)
    val check = opt.Check()
    // println(check, obj, objExpr)
    // println(getAssertions)
    try {
      Integer.parseInt(objExpr.toString)
    } catch {
      case e: Exception => Integer.MAX_VALUE
    }
  }

  override def toString: String = solver.getAssertions.foldLeft("") { (acc, assertion) => acc+assertion+"\n"}
}

object Z3Solver {
  var TOTAL_TIME: Double = 0
  var TOTAL_QUERY: Int = 0

  def printTime(): Unit = Utils.printRedString("Z3's total time is: "+("%.3f" format TOTAL_TIME)+"s for " + TOTAL_QUERY + " queries")
}