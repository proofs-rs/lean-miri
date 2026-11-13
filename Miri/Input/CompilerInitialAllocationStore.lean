import Miri.Input.CompilerInitialAllocationWorld

/-! The authoritative typed store is held in actual execution-owned User state.
Memory is deliberately NOT cached here; every access pairs this store with the
current MachineHooks memory, whose shared reserve boundary owns raw IDs. -/
namespace Miri.Input.CompilerInitialAllocation
open Miri.Memory
set_option autoImplicit false
variable {P E K : Type}
structure Store where
  runs : Array (Nat × UInt64)
  crosswalk : Array (SourceIdentity × AllocId)
  typedDedup : Array TypedDedup
  symbolic : Array (AllocId × GlobalKey)
def AllocatorWorld.store (world : AllocatorWorld P E K) : Store :=
  ⟨world.runs,world.crosswalk,world.typedDedup,world.symbolic⟩
def Store.withMemory (store : Store) (memory : MemoryState P E K) : AllocatorWorld P E K :=
  -- Runtime/local allocations advance only MemoryState. Reconstruct identity
  -- views from that authority; the retained store must never rewind a counter
  -- or lose a local allocation's raw/runtime crosswalk on its next byte query.
  {memory,
   runs := memory.initialCompilerRuns.map (fun row => (row.token,row.next)),
   crosswalk := memory.initialCompilerBindings.map (fun row => (⟨row.run,row.source⟩,row.runtime)),
   typedDedup := store.typedDedup,symbolic := store.symbolic}
end Miri.Input.CompilerInitialAllocation
