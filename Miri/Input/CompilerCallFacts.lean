import Miri.Input.CompilerIntrinsicFacts

/-! call.rs find_mir_or_eval_fn and noncapturing-closure source predicates.
Exact full-instance evidence supplies compiler symbol spelling; neither source
definition paths nor debug displays substitute for tcx.symbol_name(instance).
-/
namespace Miri.Input.CompilerCallFacts
open Lean Miri.Interpreter
private def entry (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String RuntimeInstanceData := do
  let some value := p.entries.find? (·.callee == callee) | throw "missing exact full-instance call facts"
  pure value.data

def isForeignItem (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Bool :=
  return (← entry p callee).foreignItem

def isClosureLike (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Bool :=
  return (← entry p callee).closureLike

def symbolName (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String String := do
  (← entry p callee).symbolName

def codegenSymbolName (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String (Option String) := do
  (← entry p callee).codegenSymbolName
end Miri.Input.CompilerCallFacts
