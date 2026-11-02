import duplicate_prefix.S04ReturnWildcardOrderedRestore
import duplicate_prefix.S04ReturnReleaseVariants
import duplicate_prefix.GeneralBorrowBothProtectorRelease

namespace DuplicatePrefix.S04ActiveSeparateWildcardReturnPop
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual pop of a separate active positive source protector followed by
the return protector. The source release performs its real associated Read
callbacks and may change its tree; no Quiescent or release-success premise. -/
theorem pop_active_separate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (sourceId returnId : AllocId) (separate : returnId ≠ sourceId)
    (sourceEntry returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (returnLive : machine.memory.live.find? (fun row => row.1 == returnId) = some (returnId,returnEntry))
    (sourceTag returnTag : BorTag) (sourceChild sourceSelected child : UniIndex)
    (sourceMaximum : Option BorTag) (sourceOffset sourceLen offset : UInt64)
    (sourceNode returnNode : TreeNode)
    (sourceTagged : sourceEntry.allocation.extra.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen)
    (sourceDistinct : sourceEntry.allocation.extra.roots.toList.Nodup)
    (sourceOrder : ∀ valid : 0 < sourceEntry.allocation.extra.roots.size,
      sourceSelected ≠ sourceEntry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra)
    (sourceShort : sourceEntry.allocation.extra.nodes.size < 65536)
    (sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceChild .Write
      sourceOffset (sourceOffset+sourceLen))
    (returnTagged : returnEntry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : returnEntry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (parentless : returnNode.parent = none)
    (leaf : returnNode.children = #[])
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(sourceId,sourceTag),(returnId,returnTag)])
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame returnEntry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts returnEntry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive returnEntry.allocation.extra tracker.global.protectedTags
      (some child) (some child) (some returnTag) offset 1)
    (distinct : returnEntry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder returnEntry.allocation.extra)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound returnEntry.allocation.extra returnTag)
    (notPrimary : ∀ valid : 0 < returnEntry.allocation.extra.roots.size, returnEntry.allocation.extra.roots[0] ≠ child)
    (short : returnEntry.allocation.extra.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin returnEntry.allocation.extra child .Write offset (offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let sourceReleased := (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
    let released := (returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let memory := StackPopRelease.commitTree
      (StackPopRelease.commitTree machine.memory sourceId sourceEntry sourceReleased)
      returnId returnEntry released
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame
        (ActualPopPlan.released machine memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released (tracker.global.endCall borrowFrame) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released
      (tracker.global.endCall borrowFrame).protectedTags none none none offset 1) := by
  have ownedReturn : (returnId,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨returnDone,afterRuntime,parentPositive,_,_⟩ := S04ReturnWildcardOrderedRestore.release_to_wildcard
    returnEntry.allocation.extra tracker.global borrowFrame runtime order returnId returnTag child offset 1 exposed
    positive returnNode returnPresent returnSame parentless leaf returnHidden returnTagged ownedReturn hiddenFrame notPrimary distinct short activity
  let released := (returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  have returnRelease : returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : returnEntry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at returnDone
      cases returnDone
      simp only [released,h]
  obtain ⟨sourceDone,_sourceRuntime,_sourcePositive,_sourceActivity,_sourceFrame,_sourceCapacity⟩ :=
    GeneralBorrowBothProtectorRelease.release sourceEntry.allocation.extra tracker.global sourceRuntime
      sourceTag sourceChild sourceSelected sourceMaximum sourceOffset sourceLen sourcePositive
      sourceNode sourcePresent sourceHidden sourceTagged sourceDistinct sourceOrder sourceShort sourceActivity
  let sourceReleased := (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
  have sourceRelease : sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags =
      ⟨sourceReleased,.Released⟩ := by
    cases h : sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at sourceDone
      cases sourceDone
      simp only [sourceReleased,h]
  have nextLive := StackPopRelease.lookup_commit_other machine.memory sourceId returnId sourceEntry returnEntry
    sourceReleased separate returnLive
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (StackPopRelease.commitTree
        (StackPopRelease.commitTree machine.memory sourceId sourceEntry sourceReleased)
        returnId returnEntry released) := by
    rw [owned]
    exact .live sourceId sourceTag sourceEntry sourceReleased [(returnId,returnTag)] machine.memory _
      sourceLive sourceRelease
      (.live returnId returnTag returnEntry released [] _ _ nextLive returnRelease (.nil _))
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,parentPositive⟩

end
end DuplicatePrefix.S04ActiveSeparateWildcardReturnPop

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S04ActiveSeparateWildcardReturnPop.pop_active_separate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved active separate return pop dependency {dependency}"
