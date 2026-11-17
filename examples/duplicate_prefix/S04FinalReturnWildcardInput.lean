import duplicate_prefix.S03PhysicalReturnInput
import duplicate_prefix.S04FinalReturnVariantsInput
import duplicate_prefix.S04ReturnWildcardOrderedRestore

namespace DuplicatePrefix.S04FinalReturnWildcardInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnVariantsInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- CURRENT original wildcard destination metadata, independent of permission
and operation success. Byte fields describe the actual result of the body. -/
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
  wildcard : pointer.provenance = .wildcard
  mode : before.user.addresses.provenanceMode ≠ .strict
  exposed : before.user.addresses.exposed.contains id = true
  geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap pointer.offset.bytes
    base id entry.allocation.byteSize

/-- Exact post-pop metadata transport for the original wildcard pointer.
Permission is the derived release result, never a future Input premise. -/
def after_release {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (destination : Destination machine place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (priorMemory : MemoryState Provenance BorrowTree MiriMemoryKind) (released : BorrowTree) (index : Nat)
    (capacity : released.locations.size = destination.entry.allocation.extra.locations.size)
    (positive : DuplicatePrefixBorrowAuthorization.Positive released (tracker.global.endCall borrowFrame).protectedTags
      none none none destination.offset 1) :
    S03PhysicalReturnInput.Input
      (S04FinalReturnVariantsInput.afterPop frames frame machine tracker borrowFrame priorMemory destination.id destination.entry released index).machine place := by
  let result := S04FinalReturnVariantsInput.afterPop frames frame machine tracker borrowFrame priorMemory destination.id destination.entry released index
  have memory : result.machine.memory = StackPopRelease.commitTree priorMemory destination.id destination.entry released := by
    unfold result S04FinalReturnVariantsInput.afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have user : result.machine.user = machine.user := by
    unfold result S04FinalReturnVariantsInput.afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have enabled : result.machine.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} := by
    unfold result S04FinalReturnVariantsInput.afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
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
    borrowSize := ?_, source := none, selectedRoot := none, maximum := none,
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
    simp only [DuplicatePrefixReferenceInput.Binding,destination.wildcard]
    exact ⟨trivial,destination.mode,destination.exposed,destination.geometry⟩

/-- Actual configured pop for all current empty-argument protector placements:
absent, same allocation, or separate allocation. Permission restoration uses
ordinary child Positive plus the preserved exposed cutoff and parent order. -/
theorem pop
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (returnTag : BorTag) (child : UniIndex) (returnNode : TreeNode) (offset : UInt64)
    (returnTagged : entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (parentless : returnNode.parent = none)
    (leaf : returnNode.children = #[]) (returnHidden : returnNode.isExposed = false)
    (argument : ArgumentProtection machine.memory borrowFrame id entry returnTag)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      (some child) (some child) (some returnTag) offset 1)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound entry.allocation.extra returnTag)
    (notPrimary : ∀ valid : 0 < entry.allocation.extra.roots.size, entry.allocation.extra.roots[0] ≠ child)
    (short : entry.allocation.extra.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra child .Write offset (offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let released := (entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let memory := StackPopRelease.commitTree argument.priorMemory id entry released
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame (ActualPopPlan.released machine memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released (tracker.global.endCall borrowFrame) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released (tracker.global.endCall borrowFrame).protectedTags
      none none none offset 1) := by
  obtain ⟨done,afterRuntime,finalPositive,shape,capacity⟩ := S04ReturnWildcardOrderedRestore.release_to_wildcard
    entry.allocation.extra tracker.global borrowFrame runtime order id returnTag child offset 1 exposed positive
    returnNode returnPresent returnSame parentless leaf returnHidden returnTagged argument.owned_return hiddenFrame
    notPrimary distinct short activity
  let released := (entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  have returnRelease : entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at done
      cases done
      simp only [released,h]
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (StackPopRelease.commitTree argument.priorMemory id entry released) := by
    cases argument with
    | only owned =>
      rw [owned]
      exact .live id returnTag entry released [] machine.memory _ live returnRelease (.nil _)
    | same zeroTag zeroIndex zeroNode owned zeroTagged zeroPresent zeroHidden quiet =>
      have zeroRelease := S04ReturnReleaseInactive.release entry.allocation.extra zeroTag zeroIndex zeroNode
        zeroTagged zeroPresent zeroHidden quiet tracker.global.protectedTags
      have identity : ({entry with allocation := entry.allocation.setExtra entry.allocation.extra} :
          LocalAllocation Provenance BorrowTree MiriMemoryKind) = entry := by
        cases entry with
        | mk kind allocation => cases allocation;rfl
      have nextLive : (StackPopRelease.commitTree machine.memory id entry entry.allocation.extra).live.find?
          (fun row => row.1 == id) = some (id,entry) := by
        simpa only [identity] using StackPopRelease.lookup_commit_same machine.memory id entry entry.allocation.extra
      rw [owned]
      exact .live id zeroTag entry entry.allocation.extra [(id,returnTag)] machine.memory _ live zeroRelease
        (.live id returnTag entry released [] _ _ nextLive returnRelease (.nil _))
    | separate zeroId zeroEntry zeroTag zeroIndex zeroNode different zeroLive owned zeroTagged zeroPresent zeroHidden quiet =>
      have zeroRelease := S04ReturnReleaseInactive.release zeroEntry.allocation.extra zeroTag zeroIndex zeroNode
        zeroTagged zeroPresent zeroHidden quiet tracker.global.protectedTags
      have nextLive := StackPopRelease.lookup_commit_other machine.memory zeroId id zeroEntry entry
        zeroEntry.allocation.extra different live
      rw [owned]
      exact .live zeroId zeroTag zeroEntry zeroEntry.allocation.extra [(id,returnTag)] machine.memory _ zeroLive zeroRelease
        (.live id returnTag entry released [] _ _ nextLive returnRelease (.nil _))
    | nonlive zeroId zeroTag metadata absent owned =>
      obtain ⟨info,lookup,notLive⟩ := S03NonliveEmptyMetadata.known machine.memory zeroId none metadata absent
      rw [owned]
      exact .skip zeroId zeroTag info [(id,returnTag)] machine.memory _ lookup notLive
        (.live id returnTag entry released [] machine.memory _ live returnRelease (.nil _))
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,finalPositive⟩

end
end DuplicatePrefix.S04FinalReturnWildcardInput
