package analysis

import com.microsoft.z3.{BoolExpr, Expr}
import com.sun.source.tree._
import javax.lang.model.`type`.{TypeKind, TypeMirror}
import org.checkerframework.dataflow.cfg.block.SpecialBlock.SpecialBlockType
import org.checkerframework.dataflow.cfg.block._
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.javacutil.TreeUtils
import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import utils.{GraphUtil, Utils}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
// Weakest precondition computation over a graph, instead of an AST
object PredTrans {
  val DEBUG_SMTLIB = false
  val DEBUG_TRANS_EXPR = false
  val DEBUG = false
  val DEBUG_WLP_LOOP = DEBUG
  val DEBUG_WLP_PROG = DEBUG
  val DEBUG_WLP_BLOCK = false

  // Compute the weakest precondition of a given predicate over a given AST node (representing basic statements, instead of compound statements)
  def wlpBasic(tree: Tree, pred: BoolExpr, z3Solver: Z3Solver): BoolExpr = {
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
        if (variableTree.getInitializer == null) pred
        else {
          val expr = transExpr(variableTree.getInitializer, z3Solver)
          pred.substitute(x, expr).asInstanceOf[BoolExpr]
        }

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

      case expressionTree: ExpressionTree => pred
      /*val shouldVisit = isTopLevelStmt(node)
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
      }*/

      case _ => pred
    }
  }

  def wlpBlock(curBlock: Block, pred: BoolExpr, z3Solver: Z3Solver): BoolExpr = {
    curBlock match {
      case reg: RegularBlock =>
        assert(reg != null && reg.getContents != null)
        // Traverse statements backwards
        getTopLevelStmts(reg).reverse.foldLeft(pred)(
          (accPred, node) => {
            if (node.getTree != null) {
              // Compute the weakest precondition of the instruction
              val newPred = PredTrans.wlpBasic(node.getTree, accPred, z3Solver)
              if (DEBUG_WLP_BLOCK) {
                println("WLP of statement " + node.getTree + " before predicate " + accPred + " is predicate " + newPred)
                /*z3Solver.push()
                z3Solver.mkAssert(newPred)
                val res = z3Solver.checkSAT
                z3Solver.pop()
                assert(res, newPred)*/
              }
              newPred
            }
            else accPred
          })
      case _ => pred
    }
  }

  // Compute the weakest pre-condition of the given predicate (which is the post-condition at the exit node) before the program's entry points
  def wlpProg(graph: Graph[Block, DefaultEdge],
              pred: BoolExpr,
              exit: Block,
              z3Solver: Z3Solver): Map[Block, BoolExpr] = {
    // Never modify the input graph
    val graphp = GraphUtil.cloneGraph(graph)

    // Remove all outgoing edges from the input node
    // Reference: https://github.com/jgrapht/jgrapht/issues/767
    graphp.removeAllEdges(graphp.outgoingEdgesOf(exit).asScala.toList.asJava)

    // Find all root nodes
    val roots = graphp.vertexSet().asScala.filter(b => graphp.inDegreeOf(b) == 0)
    if (DEBUG_WLP_PROG) {
      println("\n\n\nInfer WLP before root blocks " + roots.map(b => b.getId) + " in program " + graphp.vertexSet().asScala.map(b => b.getId) + " with post-condition " + pred + " at exit block " + exit.getId)
    }

    roots.foldLeft(new HashMap[Block, BoolExpr])({
      (acc, root) =>
        if (DEBUG_WLP_PROG) {
          println("\n\nVisiting root: " + root.getId)
        }
        // Create yet another new graph
        val graphpp = GraphUtil.cloneGraph(graphp)

        // Remove all nodes that cannot be reached from the root or cannot reach the input node
      {
        val nodes = graphpp.vertexSet().asScala
          .filter(b => !GraphUtil.isReachable(b, exit, graphpp) || !GraphUtil.isReachable(root, b, graphpp))
        graphpp.removeAllVertices(nodes.asJava)
      }

        // SCC condensation graph
        val sccCds = GraphUtil.getSCCCondensation(graphpp)

        // Topologically sort SCCs
        val sccWlps = GraphUtil.reverseTopological(sccCds).foldLeft(new HashMap[Block, BoolExpr])({
          (acc2, scc) =>
            // Invariant: After each iteration, all root nodes of scc must have been related with a predicate

            val hasCycle = GraphUtil.hasCycle(scc)
            val nodes = scc.vertexSet().asScala
            if (DEBUG_WLP_PROG) {
              println("\nVisiting SCC: " + nodes.map(b => b.getId))
              // println(graphpp.vertexSet().asScala.map(b => b.getId).toString())
              println("Does the above SCC has cycle? " + hasCycle)
            }

            if (hasCycle) {
              // Find loop head
              val loopHead = {
                val loopHeads = nodes.filter({
                  node =>
                    val outgoingEdges = graphpp.outgoingEdgesOf(node).asScala
                    val numOfOutsideSCC = outgoingEdges.count(e => !scc.containsVertex(graphpp.getEdgeTarget(e)))
                    val numOfInsideSCC = outgoingEdges.count(e => scc.containsVertex(graphpp.getEdgeTarget(e)))
                    numOfInsideSCC == 1 && numOfOutsideSCC == 1
                })
                assert(loopHeads.size == 1, loopHeads.map(b => b.getId))
                loopHeads.head
              }

              // Find loop invariant
              val loopInv = z3Solver.mkTrue() // TODO

              // Compute the wlp at loop head
              val postPred = {
                val outgoingEdges = graphpp.outgoingEdgesOf(loopHead).asScala
                val tgtNodes = outgoingEdges.map(e => graphpp.getEdgeTarget(e))
                val outsideBlk = {
                  val outSideBlk = tgtNodes.filter(b => !scc.containsVertex(b))
                  assert(outSideBlk.size == 1)
                  outSideBlk.head
                }
                acc2.get(outsideBlk) match {
                  case Some(p_) => p_
                  case None => assert(false, "Outside block is " + outsideBlk.getId); z3Solver.mkFalse()
                }
              }

              val p = wlpLoop(scc, loopHead, loopInv, postPred, z3Solver)

              // Compute the WLPs inside program scc
              val wlps = wlpProg(scc, p, loopHead, z3Solver)

              // Remove all outgoing edges from loop head
              // val scc_p = GraphUtil.cloneGraph(scc)
              // scc_p.removeAllEdges(scc_p.outgoingEdgesOf(loopHead).asScala.toList.asJava)

              // Find nodes in scc that have incoming edges from outside scc
              val roots = {
                /*val scc_p_roots = scc_p.vertexSet().asScala.filter(b => scc_p.inDegreeOf(b) == 0)
                val scc_roots = scc.vertexSet().asScala.filter(b => scc.inDegreeOf(b) == 0)
                assert(scc_roots.subsetOf(scc_p_roots))
                scc_p_roots*/
                nodes.filter(b => {
                  val incomingEdges = graphpp.incomingEdgesOf(b).asScala
                  assert(incomingEdges.nonEmpty)
                  incomingEdges.exists(e => !nodes.contains(graphpp.getEdgeSource(e)))
                })
              }
              assert(roots.nonEmpty)
              roots.foldLeft(acc2)({
                (acc3, root) =>
                  wlps.get(root) match {
                    case Some(p_) => acc3 + (root -> p_)
                    case None => assert(false, "Root node is " + root.getId); acc3
                  }
              })
            }
            else {
              assert(nodes.size == 1)
              val node = nodes.head
              val outgoingEdges = sccCds.outgoingEdgesOf(scc).asScala
              outgoingEdges.size match {
                case 0 => acc2 + (node -> pred)
                case 1 =>
                  val nxtSCC = sccCds.getEdgeTarget(outgoingEdges.head)
                  val nxtBlk = {
                    val nxtBlks = graphpp.outgoingEdgesOf(node).asScala.map(e => graphpp.getEdgeTarget(e))
                    assert(nxtBlks.size == 1, nxtBlks.map(b => b.getId))
                    assert(nxtSCC.vertexSet().asScala.contains(nxtBlks.head))
                    nxtBlks.head
                  }

                  if (DEBUG_WLP_PROG) println("Next block is " + nxtBlk.getId + (if (DEBUG_SMTLIB) ": " + nxtBlk else ""))

                  acc2.get(nxtBlk) match {
                    case Some(p_) =>
                      val wlp = wlpBlock(node, p_, z3Solver)
                      node match {
                        case node_p: ConditionalBlock =>
                          // If node is a branching w/ one successor outside of scc,
                          // we strengthen the wlp with the conditional
                          val cond = getBranchCond(node_p, graphpp, z3Solver)
                          val tgtNodes = graphpp.outgoingEdgesOf(node_p).asScala
                            .map(e => graphpp.getEdgeSource(e))
                            .filter(n => scc.containsVertex(n))
                          assert(tgtNodes.size == 1)
                          val cond_p = if (tgtNodes.head == node_p.getThenSuccessor) cond else z3Solver.mkNot(cond)
                          acc2 + (node -> z3Solver.mkAnd(cond_p, wlp))
                        case _ => acc2 + (node -> wlp)
                      }
                    case None => assert(false, "Next block is " + nxtBlk.getId); acc2
                  }
                case 2 =>
                  val cond = getBranchCond(node.asInstanceOf[ConditionalBlock], graphpp, z3Solver)

                  val (thenNode, elseNode) = {
                    val blkOutgoingEdges = graphpp.outgoingEdgesOf(node).asScala
                    val n1 = graphpp.getEdgeTarget(blkOutgoingEdges.head)
                    val n2 = graphpp.getEdgeTarget(blkOutgoingEdges.tail.head)

                    assert(node.isInstanceOf[ConditionalBlock])
                    val asCondBlk = node.asInstanceOf[ConditionalBlock]
                    val twoSCCs = outgoingEdges.map(edge => sccCds.getEdgeTarget(edge))
                    val headSCC = twoSCCs.head
                    val headIsThen = headSCC.vertexSet().contains(asCondBlk.getThenSuccessor)
                    val headIsElse = headSCC.vertexSet().contains(asCondBlk.getElseSuccessor)
                    if (headIsThen) {
                      assert(!headIsElse)
                      (n1, n2)
                    }
                    else {
                      assert(!headIsThen)
                      (n2, n1)
                    }
                  }

                  if (DEBUG_WLP_PROG) {
                    println("Then Node: " + thenNode.getId)
                    println("Else Node: " + elseNode.getId)
                  }

                  (acc2.get(thenNode), acc2.get(elseNode)) match {
                    case (Some(p1), Some(p2)) =>
                      val wlp = z3Solver.mkAnd(
                        z3Solver.mkImplies(cond, p1),
                        z3Solver.mkImplies(z3Solver.mkNot(cond), p2)
                      )
                      acc2 + (node -> wlp)
                    case _ => assert(false, "Then node is " + thenNode.getId + ". Else node is " + elseNode.getId); acc2
                  }
                case x@_ => assert(false, "# of outgoing edges is " + x); acc2
              }
            }
        })

        /*predicates.get(root) match {
          case Some(p_) => acc + (root -> p_)
          case None => assert(false, "Root node is " + root.getId); acc
        }*/
        acc ++ sccWlps
    })
  }

  def wlpLoop(loopBody: Graph[Block, DefaultEdge],
              loopHead: Block,
              loopInv: BoolExpr,
              pred: BoolExpr,
              z3Solver: Z3Solver): BoolExpr = {
    assert(loopHead.isInstanceOf[ConditionalBlock], loopHead.toString)
    val loopBlks = loopBody.vertexSet().asScala
    if (DEBUG_WLP_LOOP) {
      println("\n\n\nInfer WLP before loop " + loopBlks.map(b => b.getId) + " with loop head at block " + loopHead.getId + " with post-condition " + pred)
    }

    // Get all assigned variables
    val assignedVars: Array[(String, TypeMirror)] = loopBlks.foldLeft(new HashSet[(String, TypeMirror)])({
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
    }).toArray

    val branching = getBranchCond(loopHead.asInstanceOf[ConditionalBlock], loopBody, z3Solver)

    // if (DEBUG_WLP_LOOP) println("Assigned vars: " + assignedVars)
    // if (DEBUG_WLP_LOOP) println("Loop condition: " + branching)

    // Find the weakest precondition when executing the loop body once
    val newGraph = GraphUtil.cloneGraph(loopBody)
    val exitBlk: SpecialBlock = new SpecialBlockImpl(SpecialBlockType.EXIT)
    newGraph.addVertex(exitBlk)
    // Break the loop by replacing all edges ending up at loop head with ending up at an empty exit block
    val backEdges = newGraph.incomingEdgesOf(loopHead).asScala.toList
    val exitNodes = backEdges.map(e => newGraph.getEdgeSource(e))
    exitNodes.foreach(n => newGraph.addEdge(n, exitBlk))
    newGraph.removeAllEdges(backEdges.asJava)

    val loopBodyWlp = {
      val wlps = wlpProg(newGraph, pred, exitBlk, z3Solver)
      wlps.get(loopHead) match {
        case Some(p_) => p_
        case None => assert(false); z3Solver.mkFalse()
      }
    }

    val body: Expr = {
      val loopCond = {
        val thenNode = loopHead.asInstanceOf[ConditionalBlock].getThenSuccessor
        val elseNode = loopHead.asInstanceOf[ConditionalBlock].getElseSuccessor
        if (loopBlks.contains(thenNode)) branching
        else {
          assert(loopBlks.contains(elseNode))
          z3Solver.mkNot(branching)
        }
      }
      val body = z3Solver.mkAnd(
        z3Solver.mkImplies(z3Solver.mkAnd(loopCond, loopInv), loopBodyWlp),
        z3Solver.mkImplies(z3Solver.mkAnd(z3Solver.mkNot(loopCond), loopInv), pred)
      )
      if (assignedVars.nonEmpty) {
        val vars = assignedVars.foldLeft((List[Expr](), List[Expr]()))({
          case (acc, (name: String, typ: TypeMirror)) =>
            val freshName = {
              var r = Utils.genRandStr()
              while (z3Solver.vars.contains(r)) {
                r = Utils.genRandStr()
              }
              r
            }
            if (typ.getKind == TypeKind.INT) {
              (z3Solver.mkIntVar(name) :: acc._1, z3Solver.mkIntVar(freshName) :: acc._2)
            }
            else if (typ.getKind == TypeKind.BOOLEAN) {
              (z3Solver.mkBoolVar(name) :: acc._1, z3Solver.mkBoolVar(freshName) :: acc._2)
            }
            else {
              assert(false, typ)
              acc
            }
        })
        z3Solver.mkForall(
          vars._2.toArray,
          body.substitute(vars._1.toArray, vars._2.toArray)
        )
      }
      else {
        body
      }
    }
    val ret = z3Solver.mkAnd(loopInv, body)
    if (DEBUG_WLP_LOOP && DEBUG_SMTLIB) println("WLP before the loop: " + ret)
    ret
  }

  // Find the branching condition. The branching block must only have one predecessor
  // Please make sure that results of function invocation are assigned to variables (instead of being directly used),
  // because function invocation will always lead to the generation of an exception handling block
  def getBranchCond(block: ConditionalBlock, graph: Graph[Block, DefaultEdge], z3Solver: Z3Solver): BoolExpr = {
    val incomingEdges = graph.incomingEdgesOf(block).asScala
    if (incomingEdges.isEmpty) return z3Solver.mkTrue()
    assert(incomingEdges.size == 1, "Conditional block " + block.getId + "'s incoming edges are: " + incomingEdges.toString())
    graph.getEdgeSource(incomingEdges.head) match {
      case reg: RegularBlock =>
        reg.getContents.asScala.last.getTree match {
          case expTree: ExpressionTree => transExpr(expTree, z3Solver).asInstanceOf[BoolExpr]
          case x@_ => assert(false, "Unexpected loop conditional: " + x.toString); z3Solver.mkTrue()
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
      case x@_ => assert(false, x.getId + "=>" + block.getId); z3Solver.mkTrue()
    }
  }

  // If there is no parent tree of this expression tree succeeding it in the same basic block
  def isTopLevelStmt(node: Node): Boolean = {
    if (node.getTree != null && node.getTree.isInstanceOf[StatementTree]) return true
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

// Reference: Hoare Logic - brief summary by C. Marche