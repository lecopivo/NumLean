import NumLean.Experimental.Meta.CCompiler.Extern
import Lean.Elab.Command

namespace NumLean.Experimental.Meta.CCompiler

open Lean Lean.Elab Lean.Elab.Command Lean.Compiler

syntax (name := compileCCmd) "#compile_c" ident : command

@[command_elab compileCCmd] def elabCompileC : Lean.Elab.Command.CommandElab := fun stx => do
  let `(command| #compile_c $id:ident) := stx | Lean.Elab.throwUnsupportedSyntax
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let decl ← liftCoreM <| LCNF.CompilerM.run (LCNF.toDecl declName)
  match compileDeclFunction decl with
  | .ok fn =>
      let c := renderFunction fn
      liftCoreM <| traceCompilation declName fn c
      Lean.logInfo c
  | .error e => throwError e


end NumLean.Experimental.Meta.CCompiler
