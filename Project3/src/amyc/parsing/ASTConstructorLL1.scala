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
      case Node('Expr ::= (VAL() :: _), List(Leaf(v), )
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

