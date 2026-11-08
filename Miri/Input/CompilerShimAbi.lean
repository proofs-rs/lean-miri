import Miri.Input.CallResolution
import Miri.Interpreter.ForeignItems

/-! Source shims/sig.rs ShimSig::as_abi. The exporter constructs the exact
compiler types (including c_void and source canonical fn_ptr wildcards), then
queries rustc fn_abi_of_fn_ptr. No target layout or type ID is synthesized. -/
namespace Miri.Input.CompilerShimAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  signature : ForeignItems.Signature
  abi : FnAbi MIR.TyId
structure Prepared where
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
def prepare (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : Except String Prepared := do
  let records ← match runtime.source.raw.getObjVal? "compiler_shim_abis" with
    | .error _ => pure #[]
    | .ok value => value.getArr?
  let mut entries := #[]
  for record in records do
    unless (← (← record.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "shim ABI query typing environment mismatch"
    let signature ← runtime.source.semanticTables.lookup .signature (← record.getObjVal? "signature") "$.compiler_shim_abis.signature"
    let convention ← (← signature.getObjVal? "calling_convention").getStr?
    let convention : CanonAbi ← match convention with
      | "C" => pure .C | "Rust" => pure .Rust
      | _ => throw "unknown compiler shim signature convention"
    unless !(← (← signature.getObjVal? "c_variadic").getBool?) do
      throw "variadic compiler shim recipe unsupported by current Signature API"
    let args ← (← (← signature.getObjVal? "arguments").getArr?).mapM fun arg => do
      descriptor (← arg.getStr?)
    let ret ← descriptor (← (← signature.getObjVal? "return").getStr?)
    let signature : ForeignItems.Signature := ⟨convention,args,ret⟩
    unless !(entries.any (·.signature == signature)) do throw "duplicate compiler shim signature key"
    let abi ← do
      let query ← record.getObjVal? "query"
      let inputs ← (← query.getObjVal? "input_types").getArr?
      unless inputs.size == args.size do throw "compiler shim type count mismatch"
      for input in inputs do
        let id ← input.getNat?
        let _ ← runtime.node id |>.mapError toString
      let outputId ← (← query.getObjVal? "output_type").getNat?
      let _ ← runtime.node outputId |>.mapError toString
      let result ← query.getObjVal? "abi_query"
      CallResolution.functionAbiJson runtime result abiCache
    entries := entries.push ⟨signature,abi⟩
  pure ⟨entries⟩

def expectedAbi (prepared : Prepared) (signature : ForeignItems.Signature) :
    Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.entries.find? (·.signature == signature)
    | throw "missing exact compiler shim signature query"
  pure entry.abi
/-- Bind the compiler query provider to the shared source shim dispatcher. -/
def hooks {P S D MD Ptr B I : Type} (prepared : Prepared) (base : ForeignItems.Hooks P S D MD Ptr B I) :
    ForeignItems.Hooks P S D MD Ptr B I :=
  { base with expectedAbi := fun signature =>
      match expectedAbi prepared signature with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerShimAbi
