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
  let records ← match runtime.source.raw.getObjVal? "compiler_named_shim_abis" with
    | .error _ => pure #[]
    | .ok value => value.getArr?
  let mut entries := #[]
  for record in records do
    let name ← (← record.getObjVal? "name").getStr?
    unless !(entries.any (·.name == name)) do throw "duplicate named compiler shim query"
    let recipe ← record.getObjVal? "recipe"
    unless (← (← recipe.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "named shim typing environment mismatch"
    let abi ← do
      let query ← recipe.getObjVal? "query"
      let result ← query.getObjVal? "abi_query"
      result.getNat?
    entries := entries.push ⟨name,abi⟩
  pure ⟨runtime,entries⟩

def expectedAbi (prepared : Prepared) (name : String) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact named compiler shim ABI query {name}"
  CallResolution.functionAbiId prepared.runtime entry.abi

def query (prepared : Prepared) (name : String) : EStateM StepError S (FnAbi MIR.TyId) :=
  match expectedAbi prepared name with
  | .ok abi => pure abi
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerNamedShimAbi
