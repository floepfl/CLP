package amyc
package codegen

import analyzer._
import ast.Identifier
import ast.SymbolicTreeModule.{And => AmyAnd, Call => AmyCall, Div => AmyDiv, Or => AmyOr, _}
import utils.{Context, Pipeline}
import wasm._
import Instructions.{Div, _}
import Utils._

// Generates WebAssembly code for an Amy program
object CodeGen extends Pipeline[(Program, SymbolTable), Module] {
  def run(ctx: Context)(v: (Program, SymbolTable)): Module = {
    val (program, table) = v

    // Generate code for an Amy module
    def cgModule(moduleDef: ModuleDef): List[Function] = {
      val ModuleDef(name, defs, optExpr) = moduleDef
      // Generate code for all functions
      defs.collect { case fd: FunDef if !builtInFunctions(fullName(name, fd.name)) =>
        cgFunction(fd, name, false)
      } ++
        // Generate code for the "main" function, which contains the module expression
        optExpr.toList.map { expr =>
          val mainFd = FunDef(Identifier.fresh("main"), Nil, TypeTree(IntType), expr)
          cgFunction(mainFd, name, true)
        }
    }

    // Generate code for a function in module 'owner'
    def cgFunction(fd: FunDef, owner: Identifier, isMain: Boolean): Function = {
      // Note: We create the wasm function name from a combination of
      // module and function name, since we put everything in the same wasm module.
      val name = fullName(owner, fd.name)
      Function(name, fd.params.size, isMain){ lh =>
        val locals = fd.paramNames.zipWithIndex.toMap
        val body = cgExpr(fd.body)(locals, lh)
        if (isMain) {
          body <:> Drop // Main functions do not return a value,
          // so we need to drop the value generated by their body
        } else {
          body
        }
      }
    }

    // Generate code for an expression expr.
    // Additional arguments are a mapping from identifiers (parameters and variables) to
    // their index in the wasm local variables, and a LocalsHandler which will generate
    // fresh local slots as required.
    def cgExpr(expr: Expr)(implicit locals: Map[Identifier, Int], lh: LocalsHandler): Code = {
      expr match {
        case IntLiteral(i) => Const(i)
        case BooleanLiteral(b) => if(b) Const(1) else Const(0)
        case StringLiteral(s) => mkString(s)
        case UnitLiteral() => Const(0) <:> Drop
        case Plus(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Add
        case Times(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Mul
        case AmyDiv(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Div
        case Minus(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Sub
        case Mod(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Rem
        case LessThan(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Lt_s
        case LessEquals(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Le_s
        case AmyAnd(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> And
        case AmyOr(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Or
        case Equals(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Eq
        case Concat(lhs: Expr, rhs: Expr) => cgExpr(lhs) <:> cgExpr(rhs) <:> Utils.concatImpl.code
        case Not(e: Expr) => Const(0) <:> cgExpr(e) <:> Sub
        case Neg(e: Expr) => cgExpr(e) <:> Eqz
        case Sequence(e1: Expr, e2: Expr) => cgExpr(e1) <:> cgExpr(e2)
        case Let(_, value: Expr, body: Expr) => cgExpr(value) <:> SetLocal(lh.getFreshLocal()) <:> cgExpr(body)
        case Ite(cond: Expr, thenn: Expr, elze: Expr) => cgExpr(cond) <:> If_i32 <:> cgExpr(thenn) <:> Else <:> cgExpr(elze) <:> End
        case Error(msg: Expr) => cgExpr(msg) <:> Unreachable
        case AmyCall(qname: QualifiedName, args: List[Expr]) =>
          args.map(e => cgExpr(e))
          Call(qname.name)

      }
    }

    Module(
      program.modules.last.name.name,
      defaultImports,
      globalsNo,
      wasmFunctions ++ (program.modules flatMap cgModule)
    )

  }
}