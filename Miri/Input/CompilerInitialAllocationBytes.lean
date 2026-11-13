import Miri.Input.CompilerInitialAllocationWorld
import Miri.Input.CompilerGlobalBytes

/-! Exact projection of a COMPLETE initial typed map into the existing byte
operation view. Lazy/materialized masks and None/Some(empty) remain distinct:
only exact allocation keys produced by allocate_bytes_dedup can match.
This is initial attachment only; synchronizing later byte insertions back into
the typed store remains required before general CTFE query admission. -/
namespace Miri.Input.CompilerInitialAllocation.Bytes
open Miri.Memory Miri.ABI
set_option autoImplicit false
variable {P E K : Type}
def prepare (program : LoweredProgram) (runtime : RuntimeMetadata) (run : Nat)
    (world : AllocatorWorld P E K) : Except String CompilerGlobalBytes.Prepared := do
  unless world.runs.any (fun row => row.1 == run) do throw "complete initial run not installed"
  if world.memory.byteGlobalKeysReady || !world.memory.byteGlobalKeys.isEmpty then
    throw "byte projection already initialized"
  let mut keys := #[]
  for row in world.typedDedup do
    if row.run == run then
      if let .memory value := row.key then
        let canonical : MemoryKey := {
          bytes := value.bytes,initMask := InitMask.new (Size.ofBytes (UInt64.ofNat value.bytes.size)) true,
          alignment := 1,mutable := false,pointerBytes := value.pointerBytes,littleEndian := value.littleEndian,
          provenance := ProvenanceMap.new }
        if value == canonical then
          if bound : row.salt.toNat < 32 then
            keys := keys.push (value.bytes,⟨row.salt.toNat,bound⟩,row.runtime)
  let strType := program.input.queries.globalBytes.strType
  let node ← (runtime.node strType).mapError toString
  unless node.shapeKind == .str do throw "initial byte str type is not source str primitive"
  pure ⟨strType,keys⟩
end Miri.Input.CompilerInitialAllocation.Bytes
