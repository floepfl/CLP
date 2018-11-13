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
      case Node('QName2 ::= _, List(_, id2)) =>
        val (name2, pos2) = constructName(id2)
        (QualifiedName(Some(name._1), name2), pos2)
      case _ => (QualifiedName(None, name._1), name._2)
    }
  }

  override def constructExpr(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('ExprSeq ::= _, List(expr2, expr)) =>
        constructExprSemicolon(expr2, expr)
      case Node('ExprSeq ::= (VAL() :: _), List(Leaf(v), param, _, value, _, body)) =>
        Let(constructParam(param), constructExpr(value), constructExpr(body)).setPos(v)
      case Node('Expr2 ::= _, List(expr3, expr2Seq)) =>
        constructExprMatch(expr3, expr2Seq)
      case Node('Expr3 ::= _, List(expr4, expr3Seq)) =>
        constructOpExpr(constructExpr(expr4), expr3Seq)
      case Node('Expr4 ::= _, List(expr5, expr4Seq)) =>
        constructOpExpr(constructExpr(expr5), expr4Seq)
      case Node('Expr5 ::= _, List(expr6, expr5Seq)) =>
        constructOpExpr(constructExpr(expr6), expr5Seq)
      case Node('Expr6 ::= _, List(expr7, expr6Seq)) =>
        constructOpExpr(constructExpr(expr7), expr6Seq)
      case Node('Expr7 ::= _, List(expr8, expr7Seq)) =>
        constructOpExpr(constructExpr(expr8), expr7Seq)
      case Node('Expr8 ::= _, List(expr9Seq, expr8Seq)) =>
        constructOpExpr(constructExpr(expr9Seq), expr8Seq)
      case Node('Expr9Seq ::= (MINUS() :: _), List(Leaf(minus), expr10)) =>
        Neg(constructExpr(expr10)).setPos(minus)
      case Node('Expr9Seq ::= (BANG() :: _), List(Leaf(bt), expr10)) =>
        Not(constructExpr(expr10)).setPos(bt)
      case Node('Expr9Seq ::= _, List(expr10)) =>
        constructExpr(expr10)
      case Node('Expr10 ::= (IF() :: _), List(Leaf(it), _, cond, _, _, thenn, _, _, _, elze, _)) =>
        Ite(
          constructExpr(cond),
          constructExpr(thenn),
          constructExpr(elze)
        ).setPos(it)
      case Node('Expr10 ::= (ERROR() :: _), List(Leaf(ert), _, msg, _)) =>
        Error(constructExpr(msg)).setPos(ert)
      case Node('Expr10 ::= ('Id :: _), List(id, expr11)) =>
        constructExpr11(id, expr11)
      case Node('Expr10 ::= List('Literal), List(lit)) =>
        constructLiteralWithoutPar(lit)
      case Node('Expr10 ::= (LPAREN() :: _), List(Leaf(l), exprParen)) =>
        constructExprParen(exprParen).setPos(l)
    }
  }

  def constructExprParen(ptreeSeq: NodeOrLeaf[Token]): Expr = {
    ptreeSeq match {
      case Node('ExprParen ::= ('ExprSeq :: _), List(exprSeq, _)) =>
        constructExpr(exprSeq)
      case _ => UnitLiteral()
    }
  }

  def constructExprSemicolon(ptreeLeft: NodeOrLeaf[Token], ptreeSeq: NodeOrLeaf[Token]): Expr = {
    ptreeSeq match {
      case Node('Expr ::= (SEMICOLON() :: _), List(s, ptreeRight)) =>
        val exprLeft = constructExpr(ptreeLeft)
        Sequence(exprLeft, constructExpr(ptreeRight)).setPos(exprLeft)
      case _ =>
        val exprLeft = constructExpr(ptreeLeft)
        exprLeft.setPos(exprLeft)
    }
  }

  def constructExprMatch(ptreeLeft: NodeOrLeaf[Token], ptreeSeq: NodeOrLeaf[Token]): Expr = {
    ptreeSeq match {
      case Node('Expr2Seq ::= (MATCH() :: _), List(_, _, cases, _)) =>
        val exprLeft = constructExpr(ptreeLeft)
        Match(exprLeft, constructCase2(cases)).setPos(exprLeft)
      case _ =>
        val exprLeft = constructExpr(ptreeLeft)
        exprLeft.setPos(exprLeft)
    }
  }

  def constructCase2(pTree: NodeOrLeaf[Token]): List[MatchCase] = {
    pTree match {
      case Node('Cases ::= _, List(c, cases2)) =>
        cases2 match {
          case Node('Cases2 ::= List('Cases), List(cases)) =>
            constructCase(c) :: constructCase2(cases)
          case Node('Cases2 ::= _, List()) =>
            List(constructCase(c))
        }
    }
  }

  def constructExpr11(ptreeLeft: NodeOrLeaf[Token], ptreeSeq: NodeOrLeaf[Token]): Expr = {
    ptreeSeq match {
      case Node('Expr11 ::= ('QName2 :: _), List(qname,_ , as, _)) =>
        val(name, pos) = constructQname2(qname, constructName(ptreeLeft))
        val args = constructList(as, constructExpr, hasComma = true)
        Call(name, args).setPos(pos)
      case _  =>
        val(name, pos) = constructName(ptreeLeft)
        Variable(name).setPos(pos)
    }
  }

  def constructLiteralWithoutPar(pTree: NodeOrLeaf[Token]): Literal[_] = {
    pTree match {
      case Node('Literal ::= List(INTLITSENT), List(Leaf(it@INTLIT(i)))) =>
        IntLiteral(i).setPos(it)
      case Node('Literal ::= List(STRINGLITSENT), List(Leaf(st@STRINGLIT(s)))) =>
        StringLiteral(s).setPos(st)
      case Node('Literal ::= _, List(Leaf(tt@TRUE()))) =>
        BooleanLiteral(true).setPos(tt)
      case Node('Literal ::= _, List(Leaf(tf@FALSE()))) =>
        BooleanLiteral(false).setPos(tf)
    }
  }

  override def constructLiteral(pTree: NodeOrLeaf[Token]): Literal[_] = {
    pTree match {
      case Node('NastyLiteral ::= List(INTLITSENT), List(Leaf(it@INTLIT(i)))) =>
        IntLiteral(i).setPos(it)
      case Node('NastyLiteral ::= List(STRINGLITSENT), List(Leaf(st@STRINGLIT(s)))) =>
        StringLiteral(s).setPos(st)
      case Node('NastyLiteral ::= _, List(Leaf(tt@TRUE()))) =>
        BooleanLiteral(true).setPos(tt)
      case Node('NastyLiteral ::= _, List(Leaf(tf@FALSE()))) =>
        BooleanLiteral(false).setPos(tf)
      case Node('NastyLiteral ::= _, List(Leaf(lp@LPAREN()), Leaf(RPAREN()))) =>
        UnitLiteral().setPos(lp)
    }
  }

  override def constructPattern(pTree: NodeOrLeaf[Token]): Pattern = {
    pTree match {
      case Node('Pattern ::= List(UNDERSCORE()), List(Leaf(u))) =>
        WildcardPattern().setPos(u)
      case Node('Pattern ::= List('NastyLiteral), List(nlit)) =>
        val literal = constructLiteral(nlit)
        LiteralPattern(literal).setPos(literal)
      case Node('Pattern ::= ('Id :: _), List(id, pattern)) =>
        constructPattern2(id, pattern)
    }
  }

  def constructPattern2(pTreeId: NodeOrLeaf[Token], ptreeRight: NodeOrLeaf[Token]): Pattern = {
    ptreeRight match {
      case Node('Pattern2 ::= ('QName2 :: _), List(qn, _, patts, _)) =>
        val name = constructName(pTreeId)
        val (qname, pos) = constructQname2(qn, name)
        val patterns = constructList(patts, constructPattern, hasComma = true)
        CaseClassPattern(qname, patterns).setPos(pos)
      case Node('Pattern2 ::= _, List()) =>
        val (name, pos) = constructName(pTreeId)
        IdPattern(name).setPos(pos)
    }
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
      case Node(sym ::= _, List(Leaf(op), rightNode))
        if Set('Expr3Seq, 'Expr4Seq, 'Expr5Seq, 'Expr6Seq, 'Expr7Seq, 'Expr8Seq) contains sym =>
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(tokenToExpr(op)(leftopd, nextAtom).setPos(leftopd), suf) // captures left associativity
        }
    }
  }

}

