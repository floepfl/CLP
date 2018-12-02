package amyc
package analyzer

import amyc.ast.NominalTreeModule.QualifiedName
import utils._
import ast.{Identifier, NominalTreeModule => N, SymbolicTreeModule => S}

// Name analyzer for Amy
// Takes a nominal program (names are plain strings, qualified names are string pairs)
// and returns a symbolic program, where all names have been resolved to unique Identifiers.
// Rejects programs that violate the Amy naming rules.
// Also populates and returns the symbol table.
object NameAnalyzer extends Pipeline[N.Program, (S.Program, SymbolTable)] {
  def run(ctx: Context)(p: N.Program): (S.Program, SymbolTable) = {
    import ctx.reporter._

    // Step 0: Initialize symbol table
    val table = new SymbolTable

    // Step 1: Add modules to table 
    val modNames = p.modules.groupBy(_.name)
    modNames.foreach { case (name, modules) =>
      if (modules.size > 1) {
        fatal(s"Two modules named $name in program", modules.head.position)
      }
    }

    modNames.keys.toList foreach table.addModule

    // Helper method: will transform a nominal type 'tt' to a symbolic type,
    // given that we are within module 'inModule'.
    def transformType(tt: N.TypeTree, inModule: String): S.Type = {
      tt.tpe match {
        case N.IntType => S.IntType
        case N.BooleanType => S.BooleanType
        case N.StringType => S.StringType
        case N.UnitType => S.UnitType
        case N.ClassType(qn@N.QualifiedName(module, name)) =>
          table.getType(module getOrElse inModule, name) match {
            case Some(symbol) =>
              S.ClassType(symbol)
            case None =>
              fatal(s"Could not find type $qn", tt)
          }
      }
    }

    // Step 2: Check name uniqueness of definitions in each module

    p.modules.foreach{case mod =>
        val names = mod.defs.map{_.name}
        if(names.toSet.size != names.size) {
          fatal(s"Two defs in module $mod have the same name", mod.defs.head.position)
        }}

    // Step 3: Discover types and add them to symbol table
    p.modules.foreach{case mod =>
      mod.defs.foreach{d => d match {
        case N.AbstractClassDef(name) => table.addType(mod.name, name)
        case _ =>
      }}
    }

    // Step 4: Discover type constructors, add them to table

    p.modules.foreach{case mod =>
      mod.defs.foreach(d => d match {
        case N.CaseClassDef(name, argTypes, parentName) =>
          val id = table.getType(mod.name, parentName)
          if(id.isDefined) {
            val list = argTypes.map { case tt => transformType(tt, mod.name) }
            table.addConstructor(mod.name, name, list, id.get)
          } else {
            fatal(s"Could not find $name", d.position)
          }
        case _ =>
      })
    }

    // Step 5: Discover functions signatures, add them to table
    p.modules.foreach{case mod =>
      mod.defs.foreach(d => d match {
        case N.FunDef(name, params, retType, _) =>
          val paramsSType = params.map{case N.ParamDef(_, tt) => transformType(tt, mod.name)}
          table.addFunction(mod.name, name, paramsSType, transformType(retType, mod.name))
        case _ =>
      })
    }

    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        val SType = table.getType(module, name)
        if (SType.isDefined)
          S.AbstractClassDef(SType.get)
        else
          fatal(s"Could not find AbstractClassDef $name inside the module $module", df.position)
      case N.CaseClassDef(name, _, _) =>
        table.getConstructor(module, name) match {
          case Some((id, ConstrSig(argTypes, parent, index))) =>
            val argTypeTree = argTypes.map(t => S.TypeTree(t))
            val Sparent = table.getType(module, parent.name)
            if(Sparent.isDefined) {
              S.CaseClassDef(id, argTypeTree, Sparent.get)
            } else {
              fatal(s"Could not find $parent in module $module concerning $name", df.position)
            }
          case None => fatal(s"Could not find $name in transformDef CaseClassDef", df.position)
        }
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"Two parameters named $name in function ${fd.name}", fd)
        }
      }

      val paramNames = params.map(_.name)

      val newParams = params zip sig.argTypes map { case (pd@N.ParamDef(name, tt), tpe) =>
        val s = Identifier.fresh(name)
        S.ParamDef(s, S.TypeTree(tpe).setPos(tt)).setPos(pd)
      }

      val paramsMap = paramNames.zip(newParams.map(_.name)).toMap

      S.FunDef(
        sym,
        newParams,
        S.TypeTree(sig.retType).setPos(retType),
        transformExpr(body)(module, (paramsMap, Map()))
      ).setPos(fd)
    }

    def SQname(qname: N.QualifiedName, module: String, position: Position, numberOfArguments: Int): S.QualifiedName = {
      qname match {
        case N.QualifiedName(None, name) =>
          val f = table.getFunction(module, name)
          val c = table.getConstructor(module, name)
          SQnameSeq(f, c, name, numberOfArguments, position)
        case N.QualifiedName(Some(mod), name) =>
          val f = table.getFunction(mod, name)
          val c = table.getConstructor(mod, name)
          SQnameSeq(f, c, name, numberOfArguments, position)
      }
    }

    def SQnameSeq(f: Option[(Identifier, FunSig)], c: Option[(Identifier, ConstrSig)], name: String, numberOfArguments: Int, position: Position): S.QualifiedName = {
      f match {
        case Some((id, funSig)) =>
          if(funSig.argTypes.size != numberOfArguments) fatal(s"Function $id has the wrong number of arguments", p)
          id
        case None => c match {
          case Some((id, constrSig)) =>
            if(constrSig.argTypes.size != numberOfArguments) fatal(s"Construtor $id has the wrong number of arguments", p)
            id
          case None => fatal(s"Could not find function or caseclass named $name", p)
        }
      }
    }
    // This function takes as implicit a pair of two maps:
    // The first is a map from names of parameters to their unique identifiers,
    // the second is similar for local variables.
    // Make sure to update them correctly if needed given the scoping rules of Amy
    def transformExpr(expr: N.Expr)
                     (implicit module: String, names: (Map[String, Identifier], Map[String, Identifier])): S.Expr = {
      val (params, locals) = names
      val res = expr match {
        case N.Match(scrut, cases) =>
          def cases_S = cases.map(transformCase(_))
          S.Match(transformExpr(scrut), cases_S).setPos(scrut.position)
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {
            pat match {
              case N.WildcardPattern() => (S.WildcardPattern().setPos(pat.position), Nil)
              case N.IdPattern(name) =>
                if(locals.contains(name)) fatal(s"$name already exists")
                val id = Identifier.fresh(name)
                (S.IdPattern(id).setPos(pat.position), List((name, id)))
              case N.LiteralPattern(lit) => lit match {
                case N.IntLiteral(i) => (S.LiteralPattern(S.IntLiteral(i)).setPos(pat.position), Nil)
                case N.BooleanLiteral(b) => (S.LiteralPattern(S.BooleanLiteral(b)).setPos(pat.position), Nil)
                case N.StringLiteral(s) => (S.LiteralPattern(S.StringLiteral(s)).setPos(pat.position), Nil)
                case N.UnitLiteral() => (S.LiteralPattern(S.UnitLiteral()).setPos(pat.position), Nil)
              }
              case N.CaseClassPattern(constr, args) =>
                val args_S = for(a <- args) yield transformPattern(a)
                val names = args_S.flatMap(_._2).map(_._1)
                if(names.size != names.toSet.size) {
                  fatal("Found two identical variables name in a case pattern")
                }
                val s = SQname(constr, module, pat.position, args.size)
                (S.CaseClassPattern(s, args_S.map(_._1)).setPos(pat.position), args_S.flatMap(_._2))
            }
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            S.MatchCase(newPat, transformExpr(rhs)(module, (params, locals ++ moreLocals)))
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))

        case N.Variable(name) =>
          if(locals.contains(name)) {
            S.Variable(locals(name))
          } else if(params.contains(name)) {
            S.Variable(params(name))
          } else {
            fatal(s"Didn't find variable $name", expr.position)
          }
        case N.IntLiteral(i) => S.IntLiteral(i)
        case N.BooleanLiteral(b) => S.BooleanLiteral(b)
        case N.StringLiteral(s) => S.StringLiteral(s)
        case N.UnitLiteral() => S.UnitLiteral()
        case N.Neg(e) => S.Neg(transformExpr(e))
        case N.Not(e) => S.Not(transformExpr(e))
        case N.Times(lhs, rhs) => S.Times(transformExpr(lhs), transformExpr(rhs))
        case N.And(lhs, rhs) => S.And(transformExpr(lhs), transformExpr(rhs))
        case N.Mod(lhs, rhs) => S.Mod(transformExpr(lhs), transformExpr(rhs))
        case N.Div(lhs, rhs) => S.Div(transformExpr(lhs), transformExpr(rhs))
        case N.Concat(lhs, rhs) => S.Concat(transformExpr(lhs), transformExpr(rhs))
        case N.Equals(lhs, rhs) => S.Equals(transformExpr(lhs), transformExpr(rhs))
        case N.Or(lhs, rhs) => S.Or(transformExpr(lhs), transformExpr(rhs))
        case N.LessEquals(lhs, rhs) => S.LessEquals(transformExpr(lhs), transformExpr(rhs))
        case N.LessThan(lhs, rhs) => S.LessThan(transformExpr(lhs), transformExpr(rhs))
        case N.Minus(lhs, rhs) => S.Minus(transformExpr(lhs), transformExpr(rhs))
        case N.Plus(lhs, rhs) => S.Plus(transformExpr(lhs), transformExpr(rhs))
        case N.Call(qname, args) =>
          val sQname = SQname(qname, module, expr.position, args.size)
          val sArgs = args.map(transformExpr(_))
          S.Call(sQname, sArgs)
        case N.Sequence(s1, s2) => S.Sequence(transformExpr(s1), transformExpr(s2))
        case N.Let(df, value, body) =>
          val name = df.name
          if(locals.contains(df.name)) fatal(s"Variable $name already defined", df.position)
          val identifierDf = Identifier.fresh(df.name)
          val Sdf = S.ParamDef(identifierDf, S.TypeTree(transformType(df.tt, module)))
          val SValue = transformExpr(value)
          S.Let(Sdf, SValue, transformExpr(body)(module, (params, locals + (df.name -> identifierDf))))
        case N.Ite(cond, thenn, elze) =>
          S.Ite(transformExpr(cond), transformExpr(thenn), transformExpr(elze))
        case N.Error(msg) => S.Error(transformExpr(msg))
      }
      res.setPos(expr)
    }

    // Putting it all together to construct the final program for step 6.
    val newProgram = S.Program(
      p.modules map { case mod@N.ModuleDef(name, defs, optExpr) =>
        S.ModuleDef(
          table.getModule(name).get,
          defs map (transformDef(_, name)),
          optExpr map (transformExpr(_)(name, (Map(), Map())))
        ).setPos(mod)
      }
    ).setPos(p)

    (newProgram, table)

  }
}
