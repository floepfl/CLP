package amyc
package analyzer

import utils._
import ast.SymbolicTreeModule._
import ast.Identifier

// The type checker for Amy
// Takes a symbolic program and rejects it if it does not follow the Amy typing rules.
object TypeChecker extends Pipeline[(Program, SymbolTable), (Program, SymbolTable)] {

  def run(ctx: Context)(v: (Program, SymbolTable)): (Program, SymbolTable) = {
    import ctx.reporter._

    val (program, table) = v

    case class Constraint(found: Type, expected: Type, pos: Position)

    // Represents a type variable.
    // It extends Type, but it is meant only for internal type checker use,
    //  since no Amy value can have such type.
    case class TypeVariable private (id: Int) extends Type
    object TypeVariable {
      private val c = new UniqueCounter[Unit]
      def fresh(): TypeVariable = TypeVariable(c.next(()))
    }

    // Generates typing constraints for an expression `e` with a given expected type.
    // The environment `env` contains all currently available bindings (you will have to
    //  extend these, e.g., to account for local variables).
    // Returns a list of constraints among types. These will later be solved via unification.
    def genConstraints(e: Expr, expected: Type)(implicit env: Map[Identifier, Type]): List[Constraint] = {
      
      // This helper returns a list of a single constraint recording the type
      //  that we found (or generated) for the current expression `e`
      def topLevelConstraint(found: Type): List[Constraint] =
        List(Constraint(found, expected, e.position))
      
      e match {
        case IntLiteral(_) =>
          topLevelConstraint(IntType)
        case Equals(lhs, rhs) =>
          // HINT: Take care to implement the specified Amy semantic
          val tpe = TypeVariable.fresh()
        Constraint(expected, BooleanType, e.position) :: genConstraints(lhs, tpe) ::: genConstraints(rhs, tpe)
        
        case Match(scrut, cases) =>
          // Returns additional constraints from within the pattern with all bindings
          // from identifiers to types for names bound in the pattern.
          // (This is analogous to `transformPattern` in NameAnalyzer.)
          def handlePattern(pat: Pattern, scrutExpected: Type):
            (List[Constraint], Map[Identifier, Type]) =
          {
            ???  // TODO
          }

          def handleCase(cse: MatchCase, scrutExpected: Type): List[Constraint] = {
            val (patConstraints, moreEnv) = handlePattern(cse.pat, scrutExpected)
            ???  // TODO
          }

          val st = TypeVariable.fresh()
          genConstraints(scrut, st) ++ cases.flatMap(cse => handleCase(cse, st))

        case Times(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: (Constraint(IntType, expected, e.position) :: genConstraints(rhs, IntType))
        case And(lhs, rhs) =>
          genConstraints(lhs, BooleanType) ::: (Constraint(BooleanType, expected, e.position) :: genConstraints(rhs, BooleanType))
        case Mod(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: (Constraint(IntType, expected, e.position) :: genConstraints(rhs, IntType))
        case Div(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: (Constraint(IntType, expected, e.position) :: genConstraints(rhs, IntType))
        case Concat(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: (Constraint(IntType, expected, e.position) :: genConstraints(rhs, IntType))
        case Or(lhs, rhs) =>
          genConstraints(lhs, BooleanType) ::: (Constraint(BooleanType, expected, e.position) :: genConstraints(rhs, BooleanType))
        case LessEquals(lhs, rhs) =>
          genConstraints(lhs, BooleanType) ::: (Constraint(BooleanType, expected, e.position) :: genConstraints(rhs, BooleanType))
        case LessThan(lhs, rhs) =>
          genConstraints(lhs, BooleanType) ::: (Constraint(BooleanType, expected, e.position) :: genConstraints(rhs, BooleanType))
        case Minus(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: (Constraint(IntType, expected, e.position) :: genConstraints(rhs, IntType))
        case Plus(lhs, rhs) =>
          genConstraints(lhs, IntType) ::: (Constraint(IntType, expected, e.position) :: genConstraints(rhs, IntType))
        case BooleanLiteral(_) => topLevelConstraint(BooleanType)
        case StringLiteral(_) => topLevelConstraint(StringType)
        case UnitLiteral() => topLevelConstraint(UnitType)
        case Neg(e) => Constraint(IntType, expected, e.position) :: genConstraints(e, IntType)
        case Not(e) => Constraint(BooleanType, expected, e.position) :: genConstraints(e, BooleanType)
        case Call(qname, args) =>
          val funSig = table.getFunction(qname)
          val constrSig = table.getConstructor(qname)
          val tpe = env(qname)
          if(funSig.isDefined) {
            val argsAndTypes = args.zip(funSig.get.argTypes)
            val argsConstraint = argsAndTypes.flatMap{case(expr, t) => genConstraints(expr, t)}
            Constraint(tpe, expected, e.position) :: argsConstraint
          } else {
            val argsAndConstr = args.zip(constrSig.get.argTypes)
            val argsConstraint = argsAndConstr.flatMap{case(expr, t) => genConstraints(expr, t)}
            Constraint(tpe, expected, e.position) :: argsConstraint
          }
        case Sequence(s1, s2) =>
          genConstraints(s1, TypeVariable.fresh()) ::: genConstraints(s2, expected)
        case Let(df, value, body) =>
          genConstraints(value, df.tt.tpe) ::: genConstraints(body, expected)(env + (df.name -> df.tt.tpe))
        case Ite(cond, thenn, elze) =>
          genConstraints(cond, BooleanType) ::: genConstraints(thenn, expected) ::: genConstraints(elze, expected)
        case Error(msg) => genConstraints(msg, StringType)
        case Variable(name) => List(Constraint(env(name), expected, e.position))

      }
    }


    // Given a list of constraints `constraints`, replace every occurence of type variable
    //  with id `from` by type `to`.
    def subst_*(constraints: List[Constraint], from: Int, to: Type): List[Constraint] = {
      // Do a single substitution.
      def subst(tpe: Type, from: Int, to: Type): Type = {
        tpe match {
          case TypeVariable(`from`) => to
          case other => other
        }
      }

      constraints map { case Constraint(found, expected, pos) =>
        Constraint(subst(found, from, to), subst(expected, from, to), pos)
      }
    }

    // Solve the given set of typing constraints and
    //  call `typeError` if they are not satisfiable.
    // We consider a set of constraints to be satisfiable exactly if they unify.
    def solveConstraints(constraints: List[Constraint]): Unit = {
      constraints match {
        case Nil => ()
        case Constraint(found, expected, pos) :: more =>
          // HINT: You can use the `subst_*` helper above to replace a type variable
          //       by another type in your current set of constraints.
          ???  // TODO
      }
    }

    // Putting it all together to type-check each module's functions and main expression.
    program.modules.foreach { mod =>
      // Put function parameters to the symbol table, then typecheck them against the return type
      mod.defs.collect { case FunDef(_, params, retType, body) =>
        val env = params.map{ case ParamDef(name, tt) => name -> tt.tpe }.toMap
        solveConstraints(genConstraints(body, retType.tpe)(env))
      }

      // Type-check expression if present. We allow the result to be of an arbitrary type by
      // passing a fresh (and therefore unconstrained) type variable as the expected type.
      val tv = TypeVariable.fresh()
      mod.optExpr.foreach(e => solveConstraints(genConstraints(e, tv)(Map())))
    }

    v

  }
}
