import Miri.Input.Decoder
import Miri.Input.CompilerInitialAllocationSymbolBridge

/-! Opt-in whole-document decoder. The legacy decoder remains a distinct
contract; this entry point requires the complete pre-query snapshot explicitly
and rejects coexistence with the prepared allocator profile. -/
namespace Miri.Input.CompilerInitialAllocation.Document
open Lean
set_option autoImplicit false
structure Decoded where
  input : ExecutionInput
  types : TypeArena.World
  initial : Snapshot

def decode (text : String) : Except String Decoded := do
  let (input,initial,_) ← Miri.Input.decodeInitialProfiled text {}
  let types ← TypeArena.World.ofDocument input.document
  let some target := input.document.runtimeTargetDataLayout | throw "snapshot target layout absent"
  let pointerBytes := UInt64.ofNat target.defaultAddressSpacePointerSpec.pointerSizeBytes
  let littleEndian := target.endian == "little"
  let (snapshot,types) ← SymbolBridge.decode pointerBytes littleEndian initial types
  pure ⟨input,types,snapshot⟩
end Miri.Input.CompilerInitialAllocation.Document
