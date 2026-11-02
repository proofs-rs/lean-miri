import duplicate_prefix.S03PhysicalReturnInput
import duplicate_prefix.S04FinalReturnVariantsInput

namespace DuplicatePrefix.S03FinalReturnInputBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnVariantsInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Current physical metadata for the original concrete return pointer. It has
no permission or operation-success field. Body stores may change allocation
bytes; this record refers to their current result, not the original bytes. -/
structure Destination (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) where
  pointer : Pointer Provenance
  physicalPointer : place.mplace.ptr = pointer.withOptionalProvenance
  layout : place.layout = RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned = none
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  capacity : UInt64
  live : before.memory.live.find? (fun row => row.1 == id) = some (id, entry)
  cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
  pointerAddress : pointer.offset.bytes = base + offset
  nonnull : pointer.offset.bytes ≠ 0
  addressFits : base.toNat + capacity.toNat < 2^64
  bounds : offset.toNat + 1 ≤ capacity.toNat
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = Size.ofBytes capacity
  pointerBounds : ∀ row ∈ entry.allocation.provenanceMap.ptrs, row.1.bytes.toNat+8≤entry.allocation.len
  borrowSize : entry.allocation.extra.locations.size.bytes = capacity
  tag : BorTag
  parent : UniIndex
  concrete : pointer.provenance = .concrete id tag
  tagged : entry.allocation.extra.indexOfTag tag = some parent

/-- Extract physical metadata from an ordinary input without retaining its
pre-release borrowing authorization as a premise of the final write. -/
def Destination.of_input {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : S03PhysicalReturnInput.Input before place)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag) :
    Destination before place := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  let parent := Classical.choose binding.2
  have tagged := (Classical.choose_spec binding.2).2
  exact {
    pointer := input.pointer,
    physicalPointer := input.physicalPointer,
    layout := input.layout,
    aligned := input.aligned,
    id := input.id,
    entry := input.entry,
    base := input.base,
    offset := input.offset,
    capacity := input.capacity,
    live := input.live,
    cachedBase := input.cachedBase,
    pointerAddress := input.pointerAddress,
    nonnull := input.nonnull,
    addressFits := input.addressFits,
    bounds := input.bounds,
    size := input.size,
    bytes := input.bytes,
    mutable := input.mutable,
    maskValid := input.maskValid,
    maskLength := input.maskLength,
    pointerBounds := input.pointerBounds,
    borrowSize := input.borrowSize,
    tag := tag, parent := parent, concrete := concrete, tagged := tagged }

/-- Release changes only tree locations and the protector table. Reconstruct
all destination fields on that exact pop result, using its recovered parent
Positive rather than asking for a future Input. -/
def after_release {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (destination : Destination machine place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (priorMemory : MemoryState Provenance BorrowTree MiriMemoryKind) (released : BorrowTree) (index : Nat)
    (shape : released = {destination.entry.allocation.extra with locations := released.locations})
    (capacity : released.locations.size = destination.entry.allocation.extra.locations.size)
    (selected : UniIndex) (maximum : Option BorTag)
    (positive : DuplicatePrefixBorrowAuthorization.Positive released (tracker.global.endCall borrowFrame).protectedTags
      (some destination.parent) (some selected) maximum destination.offset 1) :
    S03PhysicalReturnInput.Input
      (afterPop frames frame machine tracker borrowFrame priorMemory destination.id destination.entry released index).machine place := by
  let result := afterPop frames frame machine tracker borrowFrame priorMemory destination.id destination.entry released index
  have memory : result.machine.memory = StackPopRelease.commitTree priorMemory destination.id destination.entry released := by
    unfold result afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have user : result.machine.user = machine.user := by
    unfold result afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have enabled : result.machine.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} := by
    unfold result afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have tagged : released.indexOfTag destination.tag = some destination.parent := by
    unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping shape]
    exact destination.tagged
  refine {
    tracker := {tracker with global := tracker.global.endCall borrowFrame}, enabled := enabled,
    pointer := destination.pointer, physicalPointer := destination.physicalPointer,
    layout := destination.layout, aligned := destination.aligned,
    id := destination.id,
    entry := {destination.entry with allocation := destination.entry.allocation.setExtra released},
    base := destination.base, offset := destination.offset, capacity := destination.capacity,
    live := ?_, cachedBase := ?_, pointerAddress := destination.pointerAddress,
    nonnull := destination.nonnull, addressFits := destination.addressFits, bounds := destination.bounds,
    size := destination.size, bytes := destination.bytes, mutable := destination.mutable,
    maskValid := destination.maskValid, maskLength := destination.maskLength, pointerBounds := destination.pointerBounds,
    borrowSize := ?_, source := some destination.parent, selectedRoot := some selected, maximum := maximum,
    binding := ?_, borrow := positive }
  · rw [memory]
    exact StackPopRelease.lookup_commit_same _ _ _ _
  · rw [user]
    exact destination.cachedBase
  · change released.locations.size.bytes = destination.capacity
    rw [capacity]
    exact destination.borrowSize
  · change DuplicatePrefixReferenceInput.Binding result.machine.user.addresses _ _ _ _ _ _
    rw [user]
    simp only [DuplicatePrefixReferenceInput.Binding,destination.concrete]
    exact ⟨trivial,destination.parent,rfl,tagged⟩

end
end DuplicatePrefix.S03FinalReturnInputBounds
