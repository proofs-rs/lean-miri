import Miri.Input.CallResolution
import Miri.Interpreter.ForeignItems

/-! Source shims/sig.rs ShimSig::as_abi. The exporter constructs the exact
compiler types (including c_void and source canonical fn_ptr wildcards), then
queries rustc fn_abi_of_fn_ptr. No target layout or type ID is synthesized. -/
namespace Miri.Input.CompilerShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  signature : ForeignItems.Signature
  abi : Nat
structure Prepared where
  runtime : RuntimeMetadata
  entries : Array Entry
private def descriptor (key : String) : Except String ForeignItems.SignatureType :=
  match key with
  | "unit" => pure .unit | "usize" => pure .usize | "isize" => pure .isize
  | "i32" => pure .i32 | "u32" => pure .u32
  | "pointer" => pure .pointer | "unitPointer" => pure .unitPointer
  | "alignment" => pure .alignment | "never" => pure .never
  | "u64" => pure .u64 | "u8" => pure .u8 | "bool" => pure .bool
  | "byteSlice" => pure .byteSlice | "functionPointer" => pure .functionPointer
  | _ => throw "unknown compiler shim type descriptor"
def prepare (runtime : RuntimeMetadata) : Except String Prepared := do
  let mut entries := #[]
  for record in runtime.source.queries.shimAbis.getD #[] do
    let convention : CanonAbi ← match record.signature.callingConvention with
      | "C" => pure .C | "Rust" => pure .Rust
      | _ => throw "unknown compiler shim signature convention"
    unless !record.signature.cVariadic do
      throw "variadic compiler shim recipe unsupported by current Signature API"
    let args ← record.signature.arguments.mapM descriptor
    let ret ← descriptor record.signature.result
    let signature : ForeignItems.Signature := ⟨convention, args, ret⟩
    unless !(entries.any (·.signature == signature)) do throw "duplicate compiler shim signature key"
    unless record.inputTypes.size == args.size do throw "compiler shim type count mismatch"
    for id in record.inputTypes do
      let _ ← runtime.node id |>.mapError toString
    let _ ← runtime.node record.outputType |>.mapError toString
    entries := entries.push ⟨signature, record.abiId⟩
  pure ⟨runtime, entries⟩

def expectedAbi (prepared : Prepared) (signature : ForeignItems.Signature) :
    Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.signature == signature)
    | throw "missing exact compiler shim signature query"
  CallResolution.functionAbiId prepared.runtime entry.abi
/-- Bind the compiler query provider to the shared source shim dispatcher. -/
def hooks {P S D MD Ptr B I : Type} (prepared : Prepared) (base : ForeignItems.Hooks P S D MD Ptr B I) :
    ForeignItems.Hooks P S D MD Ptr B I :=
  { base with expectedAbi := fun signature =>
      match expectedAbi prepared signature with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerShimAbi
