import Miri.Input.CallResolution
import Miri.Interpreter.ForeignItems

/-! Source shims/sig.rs ShimSig::as_abi. The exporter constructs the exact
compiler types (including c_void and source canonical fn_ptr wildcards), then
queries rustc fn_abi_of_fn_ptr. No target layout or type ID is synthesized. -/
namespace Miri.Input.CompilerShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  signature : ForeignItems.Signature
  abi : Except String (FnAbi MIR.TyId)
structure Prepared where
  entries : Array Entry

def prepare (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : Except String Prepared := do
  let records ← runtime.source.abiQueries.shims
  let mut entries := #[]
  for row in records do
    let signature := row.signature
    unless !(entries.any (·.signature == signature)) do throw "duplicate compiler shim signature key"
    let abi := row.abi.bind (fun id => CallResolution.functionAbiId runtime id abiCache)
    entries := entries.push ⟨signature,abi⟩
  pure ⟨entries⟩

def expectedAbi (prepared : Prepared) (signature : ForeignItems.Signature) :
    Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.signature == signature)
    | throw "missing exact compiler shim signature query"
  entry.abi
/-- Bind the compiler query provider to the shared source shim dispatcher. -/
def hooks {P S D MD Ptr B I : Type} (prepared : Prepared) (base : ForeignItems.Hooks P S D MD Ptr B I) :
    ForeignItems.Hooks P S D MD Ptr B I :=
  { base with expectedAbi := fun signature =>
      match expectedAbi prepared signature with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerShimAbi
