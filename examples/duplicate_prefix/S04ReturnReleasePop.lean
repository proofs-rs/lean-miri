import duplicate_prefix.S04ReturnReleaseParent
import duplicate_prefix.S04ReturnReleaseInactive
import duplicate_prefix.ActualPopPlan

namespace DuplicatePrefix.S04ReturnReleasePop
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual source-order heap effects: the empty argument is released first,
then the return destination's one-byte protector, in the SAME allocation. -/
def finalMemory (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (released : BorrowTree) : MemoryState Provenance BorrowTree MiriMemoryKind :=
  StackPopRelease.commitTree
    (StackPopRelease.commitTree machine.memory id entry entry.allocation.extra) id entry released

/-- The actual configured pop releases both tags, performs endCall, and recovers
the original concrete destination's full one-byte capability. The zero argument
may have acquired inactive stored states from the destination's earlier Write.
No success equation, release plan or future capability is a premise. -/
theorem pop_same_allocation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (zeroTag returnTag : BorTag) (zeroIndex child parent selected : UniIndex) (maximum : Option BorTag)
    (zeroNode returnNode : TreeNode) (offset : UInt64)
    (zeroTagged : entry.allocation.extra.indexOfTag zeroTag = some zeroIndex)
    (zeroPresent : entry.allocation.extra.nodeAt zeroIndex = some zeroNode)
    (zeroHidden : zeroNode.isExposed = false)
    (quiet : S04ReturnReleaseInactive.Quiescent entry.allocation.extra zeroIndex)
    (returnTagged : entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some parent)
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(id,zeroTag),(id,returnTag)])
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
    let memory := finalMemory machine id entry released
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame (ActualPopPlan.released machine memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released (tracker.global.endCall borrowFrame) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released (tracker.global.endCall borrowFrame).protectedTags
      (some parent) (some selected) maximum offset 1) := by
  have ownedReturn : (id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨done,afterRuntime,parentPositive,shape,capacity⟩ := S04ReturnReleaseParent.release_to_parent
    entry.allocation.extra tracker.global borrowFrame runtime id returnTag child parent selected maximum offset
    positive returnNode returnPresent returnSame returnEdge returnHidden returnTagged ownedReturn hiddenFrame distinct order short activity
  let released := (entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  have returnRelease : entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at done
      cases done
      simp only [released,h]
  have zeroRelease := S04ReturnReleaseInactive.release entry.allocation.extra zeroTag zeroIndex zeroNode
    zeroTagged zeroPresent zeroHidden quiet tracker.global.protectedTags
  have identity : ({entry with allocation := entry.allocation.setExtra entry.allocation.extra} :
      LocalAllocation Provenance BorrowTree MiriMemoryKind) = entry := by
    cases entry with
    | mk kind allocation => cases allocation;rfl
  have nextLive : (StackPopRelease.commitTree machine.memory id entry entry.allocation.extra).live.find?
      (fun row => row.1 == id) = some (id,entry) := by
    simpa only [identity] using StackPopRelease.lookup_commit_same machine.memory id entry entry.allocation.extra
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (finalMemory machine id entry released) := by
    rw [owned]
    exact .live id zeroTag entry entry.allocation.extra [(id,returnTag)] machine.memory _ live zeroRelease
      (.live id returnTag entry released [] _ _ nextLive returnRelease (.nil _))
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,parentPositive⟩

end
end DuplicatePrefix.S04ReturnReleasePop
