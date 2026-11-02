import duplicate_prefix.S04ReturnReleaseVariants
import duplicate_prefix.S03NonliveEmptyMetadata

namespace DuplicatePrefix.S03NonliveReturnPop
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual root pop for a Strong-registered nonlive empty argument followed
by the general return allocation. Raw metadata derives the real skip; only the
return allocation is committed. Both frame-owned tags are removed by actual
whole-frame endCall, and the return parent capability is recovered from current
runtime/access facts. This helper does not alter the existing protection enum. -/
theorem pop_nonlive_argument
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
    (argumentId : AllocId) (argumentTag : BorTag)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata machine.memory argumentId none)
    (absent : machine.memory.live.find? (fun row => row.1 == argumentId) = none)
    (owned : borrowFrame.protectedTags = #[(argumentId,argumentTag),(id,returnTag)])
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
    obtain ⟨info,lookup,notLive⟩ := S03NonliveEmptyMetadata.known machine.memory argumentId none metadata absent
    exact .skip argumentId argumentTag info [(id,returnTag)] machine.memory _ lookup notLive
      (.live id returnTag entry released [] machine.memory _ live returnRelease (.nil _))
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,parentPositive⟩


end
end DuplicatePrefix.S03NonliveReturnPop
