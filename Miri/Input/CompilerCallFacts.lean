import Miri.Input.CompilerIntrinsicFacts

/-! call.rs find_mir_or_eval_fn and noncapturing-closure source predicates.
Exact full-instance evidence supplies compiler symbol spelling; neither source
definition paths nor debug displays substitute for tcx.symbol_name(instance).
-/
namespace Miri.Input.CompilerCallFacts
open Lean Miri.Interpreter
private def entry (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Catalog.RuntimeInstance := do
  let some value := p.entries.find? (·.callee == callee) | throw "missing exact full-instance call facts"
  pure value.facts

def isForeignItem (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Bool :=
  return (← entry p callee).isForeignItem

def isClosureLike (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String Bool :=
  return (← entry p callee).isClosureLike

def symbolName (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String String := do
  let some value := (← entry p callee).symbolName | throw "compiler symbol name query absent"
  pure value

/-- LLVM source dispatch reads codegen attributes, not mangled symbol_name. -/
def codegenSymbolName (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) : Except String (Option String) := do
  let some value := (← entry p callee).codegenSymbolName | throw "compiler codegen symbol name query absent"
  pure value
end Miri.Input.CompilerCallFacts
