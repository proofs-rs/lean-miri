import Miri.Input.CallResolution
import Miri.Interpreter.ForeignItems

namespace Miri.Input.CompilerShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  signature : ForeignItems.Signature
  source : FunctionSignature
structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram
  entries : Array Entry
private def descriptor (key : String) : Except String ForeignItems.SignatureType :=
  match key with
  | "unit" => pure .unit | "usize" => pure .usize | "isize" => pure .isize
  | "i32" => pure .i32 | "u32" => pure .u32
  | "pointer" => pure .pointer | "unitPointer" => pure .unitPointer
  | "alignment" => pure .alignment | "never" => pure .never
  | "u64" => pure .u64 | "u8" => pure .u8 | "bool" => pure .bool
  | "byteSlice" => pure .byteSlice | "functionPointer" => pure .functionPointer
  | "unitPointerPointer" => pure .unitPointerPointer | "miriFrame" => pure .miriFrame
  | "f32" => pure .f32 | "f64" => pure .f64 | "i32Pointer" => pure .i32Pointer
  | _ => throw "unknown compiler shim type descriptor"
def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
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
    let source : FunctionSignature := {
      inputs := record.inputTypes, output := record.outputType, safety := .Safe
      abi := if convention == .Rust then .Rust else .C false, cVariadic := false }
    entries := entries.push ⟨signature, source⟩
  pure ⟨runtime, program, entries⟩

def expectedAbi (prepared : Prepared) (signature : ForeignItems.Signature) :
    Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.signature == signature)
    | throw "missing exact compiler shim signature query"
  SourceAbiRuntime.ofSignature prepared.runtime entry.source
/-- Bind the compiler query provider to the shared source shim dispatcher. -/
def hooks {P S D MD Ptr B I : Type} (prepared : Prepared) (base : ForeignItems.Hooks P S D MD Ptr B I) :
    ForeignItems.Hooks P S D MD Ptr B I :=
  { base with expectedAbi := fun signature =>
      match expectedAbi prepared signature with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerShimAbi
