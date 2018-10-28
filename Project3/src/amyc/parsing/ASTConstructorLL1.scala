package amyc
package parsing

import grammarcomp.parsing._
import utils.Positioned
import ast.NominalTreeModule._
import Tokens._
import amyc.ast.NominalTreeModule

// Implements the translation from parse trees to ASTs for the LL1 grammar,
// that is, this should correspond to Parser.amyGrammarLL1.
// We extend the plain ASTConstructor as some things will be the same -- you should
// override whatever has changed. You can look into ASTConstructor as an example.
class ASTConstructorLL1 extends ASTConstructor {

  // TODO: Override methods from ASTConstructor as needed
  override def constructQname(pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName ::= _, List(id, q)) =>
        val name = constructName(id)
        constructQname2(q, name)
    }
  }

  def constructQname2(pTree: NodeOrLeaf[Token], name: (String, Positioned)) : (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName2 ::= ('Id :: _), List(_, id2)) =>
        val (name2, pos2) = constructName(id2)
        (QualifiedName(Some(name._1), name2), pos2)
      case _ => (QualifiedName(None, name._1), name._2)
    }
  }

  override def constructExpr(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node(_ ::= _, List(expr, exprSeq)) =>
        constructExprSeq(expr, exprSeq)
    }
  }


  def constructExprSeq(ptreeExpr: NodeOrLeaf[Token], ptreeExprSeq: NodeOrLeaf[Token]): Expr = {
    ptreeExprSeq match {
      case Node('ExprSeq ::= (VAL() :: _), List(Leaf(v), param, _, value, _, body)) =>
        Let(constructParam(param), constructExpr(value), constructExpr(body)).setPos(v)
      case Node('ExprSeq ::= (SEMICOLON() :: _), List(Leaf(s), expr2)) =>

      case Node('Expr2Seq ::= (MATCH() :: _), List(Leaf(m), _, cases, _)) =>
        Match(constructExpr(ptreeExpr), constructList1(cases, constructCase))
      case Node('Expr3Seq ::= (OR():: _), List(Leaf(or), expr3)) =>
        tokenToExprAndSetPos(ptreeExpr, expr3, or)
      case Node('Expr4Seq ::= (AND() :: _), List(Leaf(and), expr4)) =>
        tokenToExprAndSetPos(ptreeExpr, expr4, and)
      case Node('Expr5Seq ::= (EQUALS() :: _), List(Leaf(equals), expr5)) =>
        tokenToExprAndSetPos(ptreeExpr, expr5, equals)
      case Node('Expr6Seq ::= (LESSTHAN() :: _), List(Leaf(lessThan), expr6)) =>
        tokenToExprAndSetPos(ptreeExpr, expr6, lessThan)
      case Node('Expr6Seq ::= (LESSEQUALS() :: _), List(Leaf(lessEquals), expr6)) =>
        tokenToExprAndSetPos(ptreeExpr, expr6, lessEquals)
      case Node('Expr7Seq ::= (PLUS() :: _), List(Leaf(plus), expr7)) =>
        tokenToExprAndSetPos(ptreeExpr, expr7, plus)
      case Node('Expr7Seq ::= (MINUS() :: _), List(Leaf(minus), expr7)) =>
        tokenToExprAndSetPos(ptreeExpr, expr7, minus)
      case Node('Expr7Seq ::= (CONCAT() :: _), List(Leaf(concat), expr7)) =>
        tokenToExprAndSetPos(ptreeExpr, expr7, concat)
      case Node('Expr8Seq ::= (TIMES() :: _), List(Leaf(times), expr8)) =>
        tokenToExprAndSetPos(ptreeExpr, expr8, times)
      case Node('Expr8Seq ::= (DIV() :: _), List(Leaf(div), expr8)) =>
        tokenToExprAndSetPos(ptreeExpr, expr8, div)
      case Node('Expr8Seq ::= (MOD() :: _), List(Leaf(mod), expr8)) =>
        tokenToExprAndSetPos(ptreeExpr, expr8, mod)
      case Node('Expr9Seq ::= (MINUS() :: _), List(Leaf(minus), expr10)) =>
        Neg()
      case Node('Expr10 ::= (IF() :: _), List(Leaf(i), _, eSeq2, _, _, eSeq2)) =>
        tokenToExprAndSetPos(ptreeExpr, expr8, times)
      case _ => e
    }
  }

  def tokenToExprAndSetPos(ptreeLeft: NodeOrLeaf[Token], ptreeRight: NodeOrLeaf[Token], token: Token): Expr = {
    val eLeft = constructExpr(ptreeLeft)
    val eRight = constructExpr(ptreeLeft)
    tokenToExpr(token)(eLeft, eRight).setPos(eLeft)
  }

  def constructExpr3Seq(ptree: NodeOrLeaf[Token], e: Expr): Expr = {
    ptree
  }
  /* ... */
  

  // Important helper method:
  // Because LL1 grammar is not helpful in implementing left associativity,
  // we give you this method to reconstruct it.
  // This method takes the left operand of an operator (leftopd)
  // as well as the tree that corresponds to the operator plus the right operand (ptree)
  // It parses the right hand side and then reconstruct the operator expression
  // with correct associativity.
  // If ptree is empty, it means we have no more operators and the leftopd is returned.
  // Note: You may have to override constructOp also, depending on your implementation
  def constructOpExpr(leftopd: Expr, ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node(_, List()) => //epsilon rule of the nonterminals
        leftopd
      case Node(sym ::= _, List(op, rightNode))
        if Set('OrExpr, 'AndExpr, 'EqExpr, 'CompExpr, 'AddExpr, 'MultExpr) contains sym =>
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf) // captures left associativity
        }
    }
  }

}

