import Miri.Input.CallResolution

/-! Name-keyed source shim requests whose argument types require compiler path
lookup (currently libc::pid_t CPU affinity signatures). No libc typedef is
replaced with an integer chosen by its size or diagnostic name. -/
namespace Miri.Input.CompilerNamedShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  name : String
  source : FunctionSignature
structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram
  entries : Array Entry
def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let mut entries := #[]
  for record in runtime.source.queries.namedShimAbis.getD #[] do
    unless !(entries.any (·.name == record.name)) do throw "duplicate named compiler shim query"
    let abi ← match record.recipe.signature.callingConvention with
      | "Rust" => pure ABI.ExternAbi.Rust
      | "C" => pure (.C false)
      | "System" => pure (.System false)
      | _ => throw "unsupported named source shim convention"
    let signature : FunctionSignature := {
      inputs := record.recipe.inputTypes, output := record.recipe.outputType, safety := .Safe
      abi, cVariadic := record.recipe.signature.cVariadic }
    entries := entries.push ⟨record.name, signature⟩
  pure ⟨runtime, program, entries⟩

def expectedAbi (prepared : Prepared) (name : String) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact named compiler shim ABI query {name}"
  SourceAbiRuntime.ofSignature prepared.runtime entry.source

def query (prepared : Prepared) (name : String) : EStateM StepError S (FnAbi MIR.TyId) :=
  match expectedAbi prepared name with
  | .ok abi => pure abi
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerNamedShimAbi
