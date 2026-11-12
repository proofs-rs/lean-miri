import Miri.ABI.PackedExternAbi
import Miri.Input.RawFunctionSignature

/-! Pinned FnHeader/FnSigKind stable hash source bytes. The compact source
flags hold the ABI ordinal, safety and C variadic bit; the splatted index uses
u8::MAX only for absence. These are syntax fields, not FnAbi answers. -/
namespace Miri.Input.FunctionPointerStableHash

def header (abiPacked : Nat) (safe cVariadic : Bool) (splatted : Option Nat)
    (inputCount : Nat) : Except String ByteArray := do
  let _ ← Miri.ABI.ExternAbi.ofPacked abiPacked
  RawFunctionSignature.validateSplatted inputCount splatted
  let flags := abiPacked + (if safe then 64 else 0) + (if cVariadic then 128 else 0)
  pure ⟨#[UInt8.ofNat flags, UInt8.ofNat (splatted.getD 255)]⟩
end Miri.Input.FunctionPointerStableHash
