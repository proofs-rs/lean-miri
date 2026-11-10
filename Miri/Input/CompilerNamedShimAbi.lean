import Miri.Input.CallResolution

/-! Name-keyed source shim requests whose argument types require compiler path
lookup (currently libc::pid_t CPU affinity signatures). No libc typedef is
replaced with an integer chosen by its size or diagnostic name. -/
namespace Miri.Input.CompilerNamedShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  name : String
  abi : Nat
structure Prepared where
  runtime : RuntimeMetadata
  entries : Array Entry
def prepare (runtime : RuntimeMetadata) : Except String Prepared := do
  let mut entries := #[]
  for record in runtime.source.queries.namedShimAbis.getD #[] do
    unless !(entries.any (·.name == record.name)) do throw "duplicate named compiler shim query"
    entries := entries.push ⟨record.name, record.recipe.abiId⟩
  pure ⟨runtime, entries⟩

def expectedAbi (prepared : Prepared) (name : String) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact named compiler shim ABI query {name}"
  CallResolution.functionAbiId prepared.runtime entry.abi

def query (prepared : Prepared) (name : String) : EStateM StepError S (FnAbi MIR.TyId) :=
  match expectedAbi prepared name with
  | .ok abi => pure abi
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerNamedShimAbi
