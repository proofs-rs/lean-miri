import duplicate_prefix.S04ReturnReleaseVariants
import duplicate_prefix.S04FinalReturnInput
import duplicate_prefix.S03NonliveReturnPop

namespace DuplicatePrefix.S04FinalReturnVariantsInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Current frame ownership and physical empty-argument facts. There is no
operation-success or release-plan field. The alternatives are no argument
protector, a tag in the return allocation, a tag in a separate live allocation,
or a registered nonlive argument whose actual release row is skipped. -/
inductive ArgumentProtection (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (borrowFrame : FrameState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (returnTag : BorTag) where
  | only (owned : borrowFrame.protectedTags = #[(id,returnTag)])
  | same (zeroTag : BorTag) (index : UniIndex) (node : TreeNode)
      (owned : borrowFrame.protectedTags = #[(id,zeroTag),(id,returnTag)])
      (tagged : entry.allocation.extra.indexOfTag zeroTag = some index)
      (present : entry.allocation.extra.nodeAt index = some node)
      (hidden : node.isExposed = false)
      (quiet : S04ReturnReleaseInactive.Quiescent entry.allocation.extra index)
  | separate (zeroId : AllocId) (zeroEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (zeroTag : BorTag) (index : UniIndex) (node : TreeNode)
      (different : id ≠ zeroId)
      (live : memory.live.find? (fun row => row.1 == zeroId) = some (zeroId,zeroEntry))
      (owned : borrowFrame.protectedTags = #[(zeroId,zeroTag),(id,returnTag)])
      (tagged : zeroEntry.allocation.extra.indexOfTag zeroTag = some index)
      (present : zeroEntry.allocation.extra.nodeAt index = some node)
      (hidden : node.isExposed = false)
      (quiet : S04ReturnReleaseInactive.Quiescent zeroEntry.allocation.extra index)
  | nonlive (zeroId : AllocId) (zeroTag : BorTag)
      (metadata : DuplicatePrefixEmptyReferenceInput.Metadata memory zeroId none)
      (absent : memory.live.find? (fun row => row.1 == zeroId) = none)
      (owned : borrowFrame.protectedTags = #[(zeroId,zeroTag),(id,returnTag)])

/-- Actual memory just before the final return-protector commit. -/
def ArgumentProtection.priorMemory {memory : MemoryState Provenance BorrowTree MiriMemoryKind}
    {borrowFrame : FrameState} {id : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} {returnTag : BorTag}
    (argument : ArgumentProtection memory borrowFrame id entry returnTag) :
    MemoryState Provenance BorrowTree MiriMemoryKind :=
  match argument with
  | .only _ => memory
  | .same _ _ _ _ _ _ _ _ => StackPopRelease.commitTree memory id entry entry.allocation.extra
  | .separate zeroId zeroEntry _ _ _ _ _ _ _ _ _ _ =>
      StackPopRelease.commitTree memory zeroId zeroEntry zeroEntry.allocation.extra
  | .nonlive _ _ _ _ _ => memory

theorem ArgumentProtection.owned_return {memory : MemoryState Provenance BorrowTree MiriMemoryKind}
    {borrowFrame : FrameState} {id : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} {returnTag : BorTag}
    (argument : ArgumentProtection memory borrowFrame id entry returnTag) :
    (id,returnTag) ∈ borrowFrame.protectedTags.toList := by
  cases argument with
  | only owned => rw [owned];simp
  | same _ _ _ owned _ _ _ _ => rw [owned];simp
  | separate _ _ _ _ _ _ _ owned _ _ _ _ => rw [owned];simp
  | nonlive _ _ _ _ owned => rw [owned];simp

theorem pop
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (returnTag : BorTag) (child parent selected : UniIndex) (maximum : Option BorTag)
    (returnNode : TreeNode) (offset : UInt64)
    (returnTagged : entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some parent)
    (returnHidden : returnNode.isExposed = false)
    (argument : ArgumentProtection machine.memory borrowFrame id entry returnTag)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      (some child) (some selected) maximum offset 1)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < entry.allocation.extra.roots.size,
      selected ≠ entry.allocation.extra.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
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
      (some parent) (some selected) maximum offset 1) := by
  cases argument with
  | only owned =>
      exact S04ReturnReleaseVariants.pop_return_only options limits remaining span frames frame machine tracker borrowFrame enabled frameTracked
        id entry live returnTag child parent selected maximum returnNode offset returnTagged returnPresent
        returnSame returnEdge returnHidden owned hiddenFrame runtime positive distinct order short activity thread active
  | same zeroTag zeroIndex zeroNode owned zeroTagged zeroPresent zeroHidden quiet =>
      exact S04ReturnReleasePop.pop_same_allocation
        options limits remaining span frames frame machine tracker borrowFrame enabled frameTracked
        id entry live zeroTag returnTag zeroIndex child parent selected maximum zeroNode returnNode offset
        zeroTagged zeroPresent zeroHidden quiet returnTagged returnPresent returnSame returnEdge returnHidden
        owned hiddenFrame runtime positive distinct order short activity thread active
  | separate zeroId zeroEntry zeroTag zeroIndex zeroNode separate zeroLive owned zeroTagged zeroPresent zeroHidden quiet =>
      exact S04ReturnReleaseVariants.pop_separate_allocation
        options limits remaining span frames frame machine tracker borrowFrame enabled frameTracked
        zeroId id separate zeroEntry entry zeroLive live zeroTag returnTag zeroIndex child parent selected maximum
        zeroNode returnNode offset zeroTagged zeroPresent zeroHidden quiet returnTagged returnPresent returnSame
        returnEdge returnHidden owned hiddenFrame runtime positive distinct order short activity thread active
  | nonlive zeroId zeroTag metadata absent owned =>
      exact S03NonliveReturnPop.pop_nonlive_argument options limits remaining span frames frame machine tracker borrowFrame
        enabled frameTracked id entry live returnTag child parent selected maximum returnNode offset
        returnTagged returnPresent returnSame returnEdge returnHidden zeroId zeroTag metadata absent owned
        hiddenFrame runtime positive distinct order short activity thread active

/-- The literal state returned by the actual pop theorem. -/
def afterPop (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (priorMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (released : BorrowTree) (index : Nat) : MachineHooks.State MiriMemoryKind Machine.RootUser :=
  ⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame
    (ActualPopPlan.released machine (StackPopRelease.commitTree priorMemory id entry released) tracker borrowFrame) index⟩

theorem afterPop_fields (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (priorMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (released : BorrowTree) (index : Nat) :
    (afterPop frames frame machine tracker borrowFrame priorMemory id entry released index).machine.user = machine.user ∧
    (afterPop frames frame machine tracker borrowFrame priorMemory id entry released index).machine.dataRace = machine.dataRace := by
  unfold afterPop GenericPopFrame.afterRelevanceAt
  split <;> exact ⟨rfl,rfl⟩

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
    DuplicatePrefixReturnPlaceInput.Input
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
    maskValid := destination.maskValid, maskLength := destination.maskLength, provenanceMap := destination.provenanceMap,
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
end DuplicatePrefix.S04FinalReturnVariantsInput
