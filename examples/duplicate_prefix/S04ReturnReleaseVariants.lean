import duplicate_prefix.S04ReturnReleasePop

namespace DuplicatePrefix.S04ReturnReleaseVariants
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual configured pop when empty argument retagging registered no protector.
Only the return child is released. The result recovers the original concrete
one-byte destination, from current runtime and child-access facts. This does
not establish those facts from an arbitrary original caller. -/
theorem pop_return_only
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
    (owned : borrowFrame.protectedTags = #[(id,returnTag)])
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
    let memory := StackPopRelease.commitTree machine.memory id entry released
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame (ActualPopPlan.released machine memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released (tracker.global.endCall borrowFrame) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released (tracker.global.endCall borrowFrame).protectedTags
      (some parent) (some selected) maximum offset 1) := by
  have ownedReturn : (id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨done,afterRuntime,parentPositive,_,_⟩ := S04ReturnReleaseParent.release_to_parent
    entry.allocation.extra tracker.global borrowFrame runtime id returnTag child parent selected maximum offset
    positive returnNode returnPresent returnSame returnEdge returnHidden returnTagged ownedReturn hiddenFrame distinct order short activity
  let released := (entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  have returnRelease : entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at done
      cases done
      simp only [released,h]
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (StackPopRelease.commitTree machine.memory id entry released) := by
    rw [owned]
    exact .live id returnTag entry released [] machine.memory _ live returnRelease (.nil _)
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,parentPositive⟩

/-- Exact source-order commits for distinct empty-argument and return allocations. -/
def separateMemory (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (zeroId returnId : AllocId) (zeroEntry returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (released : BorrowTree) : MemoryState Provenance BorrowTree MiriMemoryKind :=
  StackPopRelease.commitTree
    (StackPopRelease.commitTree machine.memory zeroId zeroEntry zeroEntry.allocation.extra)
    returnId returnEntry released

/-- Actual configured pop with the empty argument in a separate allocation.
Its quiescent hidden tag releases without changing its tree; the return child
is then released in the untouched destination allocation. Runtime facts and
the original concrete destination capability survive actual whole-frame endCall.
All hypotheses describe the current pre-pop state, not future success or plans. -/
theorem pop_separate_allocation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (zeroId returnId : AllocId) (separate : returnId ≠ zeroId)
    (zeroEntry returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (zeroLive : machine.memory.live.find? (fun row => row.1 == zeroId) = some (zeroId,zeroEntry))
    (returnLive : machine.memory.live.find? (fun row => row.1 == returnId) = some (returnId,returnEntry))
    (zeroTag returnTag : BorTag) (zeroIndex child parent selected : UniIndex) (maximum : Option BorTag)
    (zeroNode returnNode : TreeNode) (offset : UInt64)
    (zeroTagged : zeroEntry.allocation.extra.indexOfTag zeroTag = some zeroIndex)
    (zeroPresent : zeroEntry.allocation.extra.nodeAt zeroIndex = some zeroNode)
    (zeroHidden : zeroNode.isExposed = false)
    (quiet : S04ReturnReleaseInactive.Quiescent zeroEntry.allocation.extra zeroIndex)
    (returnTagged : returnEntry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : returnEntry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some parent)
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(zeroId,zeroTag),(returnId,returnTag)])
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame returnEntry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts returnEntry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive returnEntry.allocation.extra tracker.global.protectedTags
      (some child) (some selected) maximum offset 1)
    (distinct : returnEntry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < returnEntry.allocation.extra.roots.size,
      selected ≠ returnEntry.allocation.extra.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder returnEntry.allocation.extra)
    (short : returnEntry.allocation.extra.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin returnEntry.allocation.extra child .Write offset (offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let released := (returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let memory := separateMemory machine zeroId returnId zeroEntry returnEntry released
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame (ActualPopPlan.released machine memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released (tracker.global.endCall borrowFrame) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released (tracker.global.endCall borrowFrame).protectedTags
      (some parent) (some selected) maximum offset 1) := by
  have ownedReturn : (returnId,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨done,afterRuntime,parentPositive,_,_⟩ := S04ReturnReleaseParent.release_to_parent
    returnEntry.allocation.extra tracker.global borrowFrame runtime returnId returnTag child parent selected maximum offset
    positive returnNode returnPresent returnSame returnEdge returnHidden returnTagged ownedReturn hiddenFrame distinct order short activity
  let released := (returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  have returnRelease : returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at done
      cases done
      simp only [released,h]
  have zeroRelease := S04ReturnReleaseInactive.release zeroEntry.allocation.extra zeroTag zeroIndex zeroNode
    zeroTagged zeroPresent zeroHidden quiet tracker.global.protectedTags
  have nextLive := StackPopRelease.lookup_commit_other machine.memory zeroId returnId zeroEntry returnEntry
    zeroEntry.allocation.extra separate returnLive
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (separateMemory machine zeroId returnId zeroEntry returnEntry released) := by
    rw [owned]
    exact .live zeroId zeroTag zeroEntry zeroEntry.allocation.extra [(returnId,returnTag)] machine.memory _ zeroLive zeroRelease
      (.live returnId returnTag returnEntry released [] _ _ nextLive returnRelease (.nil _))
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,parentPositive⟩

end
end DuplicatePrefix.S04ReturnReleaseVariants
