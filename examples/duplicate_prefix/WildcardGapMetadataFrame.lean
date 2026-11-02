import duplicate_prefix.WildcardGapAddress
import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.WildcardGapMetadataFrame
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def SizesSame {K : Type} (before after : MemoryState Provenance BorrowTree K) : Prop :=
  ∀ id, (after.getAllocInfo id).toOption.map (·.size) = (before.getAllocInfo id).toOption.map (·.size)

def replace {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (allocation : Allocation Provenance BorrowTree) :
    MemoryState Provenance BorrowTree K :=
  {memory with live := (memory.live.filter fun row => row.1 != id).push (id,{entry with allocation})}

/-- Actual live replacement preserves all canonical allocation-size metadata
when the replaced allocation's byteSize is unchanged. -/
theorem replace_sizes {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (allocation : Allocation Provenance BorrowTree)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : allocation.byteSize = entry.allocation.byteSize) : SizesSame memory (replace memory id entry allocation) := by
  intro query
  by_cases same : query = id
  · subst query
    have live : (replace memory id entry allocation).live.find? (fun row => row.1 == id) =
        some (id,{entry with allocation}) := MemoryCopyBridge.live_lookup_replaced memory id _
    rw [WildcardGapAddress.size_of_live _ id _ live,WildcardGapAddress.size_of_live memory id entry present]
    rw [size]
  · have keep : allocation.setExtra allocation.extra = allocation := by cases allocation;rfl
    have metadata := StackPopRelease.metadata_commit_other memory id query {entry with allocation} allocation.extra same
    simp only [StackPopRelease.commitTree,keep] at metadata
    change (replace memory id entry allocation).getAllocInfo query = memory.getAllocInfo query at metadata
    rw [metadata]

/-- Exact return-slot entry retag and replacement preserve size metadata for
all allocations, including the return allocation itself. -/
theorem entered_sizes (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (RootZeroInvocationState.child tracker fresh).value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (root : BorTag)
    (allocation : Allocation Provenance BorrowTree)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : allocation.byteSize = entry.allocation.byteSize) :
    SizesSame machine.memory (RootZeroInvocationState.enteredMachine machine tracker fresh fresh2 id entry root allocation).memory := by
  have memoryEq : (RootZeroInvocationState.enteredMachine machine tracker fresh fresh2 id entry root allocation).memory =
      replace machine.memory id entry allocation := by
    exact MemoryCopyBridge.live_update_twice machine.memory id
      {entry with allocation := entry.allocation.setExtra (PhysicalMachineWrite.slotTree root (RootZeroInvocationState.child tracker fresh) 1 false)}
      {entry with allocation}
  rw [memoryEq]
  exact replace_sizes machine.memory id entry allocation present size

/-- Geometry is transported using size metadata preservation alone; actual
allocation extras, bytes and tag histories need not be equal. -/
theorem geometry {K : Type} (entries : Array Miri.Memory.AllocAddresses.InverseAddressEntry) (address : UInt64)
    (before after : MemoryState Provenance BorrowTree K) (same : SizesSame before after)
    (initial : WildcardGapAddress.Geometry entries address (fun id => (before.getAllocInfo id).toOption.map (·.size))) :
    WildcardGapAddress.Geometry entries address (fun id => (after.getAllocInfo id).toOption.map (·.size)) := by
  intro row member
  obtain ⟨different,outside⟩ := initial row member
  refine ⟨different,?_⟩
  intro earlier
  obtain ⟨size,known,bounds⟩ := outside earlier
  exact ⟨size,(same row.allocId).trans known,bounds⟩

end DuplicatePrefix.WildcardGapMetadataFrame
