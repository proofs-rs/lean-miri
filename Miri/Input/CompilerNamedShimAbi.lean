import Miri.Input.CallResolution

/-! Name-keyed source shim requests whose argument types require compiler path
lookup (currently libc::pid_t CPU affinity signatures). No libc typedef is
replaced with an integer chosen by its size or diagnostic name. -/
namespace Miri.Input.CompilerNamedShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  name : String
  abi : Except String (FnAbi MIR.TyId)
structure Prepared where
  entries : Array Entry

def prepare (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : Except String Prepared := do
  let records ← runtime.source.abiQueries.namedShims
  let mut entries := #[]
  for row in records do
    let name := row.name
    unless !(entries.any (·.name == name)) do throw "duplicate named compiler shim query"
    let abi := row.abi.bind (fun id => CallResolution.functionAbiId runtime id abiCache)
    entries := entries.push ⟨name,abi⟩
  pure ⟨entries⟩

def expectedAbi (prepared : Prepared) (name : String) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact named compiler shim ABI query {name}"
  entry.abi

def query (prepared : Prepared) (name : String) : EStateM StepError S (FnAbi MIR.TyId) :=
  match expectedAbi prepared name with
  | .ok abi => pure abi
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerNamedShimAbi
