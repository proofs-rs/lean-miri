import duplicate_prefix.WildcardGapMetadataFrame
import duplicate_prefix.WildcardUnexposedInteriorAddress
import duplicate_prefix.WildcardImmediateGapAddress

namespace DuplicatePrefix.WildcardGapResolver
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw metadata-backed unresolved geometry: either every predecessor lies
outside its allocation, OR only the selected predecessor is outside, or the
selected predecessor is unexposed. Both original legacy cases remain accepted. Public
wrappers form this data from size rows; resolver success is never an input. -/
def Miss {K : Type} (addresses : GlobalAddressState) (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (address : UInt64) : Prop :=
  (WildcardGapAddress.Geometry addresses.intToPtrMap address (fun id => (memory.getAllocInfo id).toOption.map (·.size)) ∨
    WildcardImmediateGapAddress.Geometry addresses.intToPtrMap address (fun id => (memory.getAllocInfo id).toOption.map (·.size))) ∨
    WildcardUnexposedInteriorAddress.Geometry addresses address (fun id => (memory.getAllocInfo id).toOption.map (·.size))

theorem resolve_miss {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : Miss before.machine.user.addresses before.machine.memory address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok none before := by
  rcases miss with gap | interior
  · rcases gap with global | immediate
    · exact WildcardGapAddress.resolve pointers before address mode global
    · exact WildcardImmediateGapAddress.resolve pointers before address mode immediate
  · exact WildcardUnexposedInteriorAddress.resolve pointers before address mode interior

/-- Exact return-slot retag/replacement preserves the data miss condition. -/
theorem entered (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (RootZeroInvocationState.child tracker fresh).value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) (root : BorTag)
    (allocation : Allocation Provenance Miri.TreeBorrows.BorrowTree)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : allocation.byteSize = entry.allocation.byteSize) (address : UInt64)
    (initial : Miss machine.user.addresses machine.memory address) :
    Miss (RootZeroInvocationState.enteredMachine machine tracker fresh fresh2 id entry root allocation).user.addresses
      (RootZeroInvocationState.enteredMachine machine tracker fresh fresh2 id entry root allocation).memory address := by
  have same := WildcardGapMetadataFrame.entered_sizes machine tracker fresh fresh2 id entry root allocation present size
  rcases initial with gap | interior
  · rcases gap with global | immediate
    · exact Or.inl (Or.inl (WildcardGapMetadataFrame.geometry _ address machine.memory _ same global))
    · apply Or.inl
      apply Or.inr
      obtain ⟨position,row,rowSize,partition,rowPresent,known,outside⟩ := immediate
      exact ⟨position,row,rowSize,partition,rowPresent,(same row.allocId).trans known,outside⟩
  · apply Or.inr
    obtain ⟨position,row,rowSize,partition,rowPresent,known,unexposed⟩ := interior
    exact ⟨position,row,rowSize,partition,rowPresent,(same row.allocId).trans known,unexposed⟩

end DuplicatePrefix.WildcardGapResolver
