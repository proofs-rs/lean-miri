import duplicate_prefix.S04ReturnReleaseVariants
import duplicate_prefix.S02DisjointReleaseAuthorization

namespace DuplicatePrefix.S04ActiveSameReturnPop
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual same-allocation pop once the return child's activity has been
transported through source release. Release success and return authorization
are derived here; this staged rule is not a complete call theorem. -/
theorem pop_after_source_activity
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (sourceTag returnTag : BorTag) (sourceChild sourceSelected child parent selected : UniIndex)
    (sourceMaximum maximum : Option BorTag) (sourceOffset sourceLen offset : UInt64)
    (sourceNode returnNode : TreeNode)
    (sourceTagged : entry.allocation.extra.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : entry.allocation.extra.nodeAt sourceChild = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen)
    (sourceDistinct : entry.allocation.extra.roots.toList.Nodup)
    (sourceOrder : ∀ valid : 0 < entry.allocation.extra.roots.size,
      sourceSelected ≠ entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (sourceShort : entry.allocation.extra.nodes.size < 65536)
    (sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra sourceChild .Write
      sourceOffset (sourceOffset+sourceLen))
    (returnTagged : entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some parent)
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(id,sourceTag),(id,returnTag)])
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame entry.allocation.extra borrowFrame)
    (positive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      (some child) (some selected) maximum offset 1)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < entry.allocation.extra.roots.size,
      selected ≠ entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (short : entry.allocation.extra.nodes.size < 65536)
    (disjoint : (sourceOffset+sourceLen).toNat ≤ offset.toNat ∨ (offset+1).toNat ≤ sourceOffset.toNat)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin
      (entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree child .Write offset (offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let sourceReleased := (entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
    let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
    let memory := StackPopRelease.commitTree
      (StackPopRelease.commitTree machine.memory id entry sourceReleased)
      id {entry with allocation := entry.allocation.setExtra sourceReleased} released
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩,GenericPopFrame.afterRelevanceAt frames frame
        (ActualPopPlan.released machine memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released (tracker.global.endCall borrowFrame) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released
      (tracker.global.endCall borrowFrame).protectedTags (some parent) (some selected) maximum offset 1) := by
  let sourceReleased := (entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
  have sourceData := GeneralBorrowBothProtectorRelease.release entry.allocation.extra tracker.global sourceRuntime
    sourceTag sourceChild sourceSelected sourceMaximum sourceOffset sourceLen sourcePositive
    sourceNode sourcePresent sourceHidden sourceTagged sourceDistinct sourceOrder sourceShort sourceActivity
  have sourceDone := sourceData.1
  have sourceShape := sourceData.2.2.2.2.1
  have nodes := congrArg BorrowTree.nodes sourceShape
  have roots := congrArg BorrowTree.roots sourceShape
  have mapping := congrArg BorrowTree.tagMapping sourceShape
  change sourceReleased.nodes = entry.allocation.extra.nodes at nodes
  change sourceReleased.roots = entry.allocation.extra.roots at roots
  change sourceReleased.tagMapping = entry.allocation.extra.tagMapping at mapping
  obtain ⟨_,afterSourceRuntime,⟨afterSourcePositive⟩⟩ := S02DisjointReleaseAuthorization.positive
    entry.allocation.extra tracker.global sourceRuntime sourceTag sourceChild sourceSelected sourceMaximum sourceOffset sourceLen
    sourcePositive sourceNode sourcePresent sourceHidden sourceTagged sourceDistinct sourceOrder sourceShort sourceActivity
    (some child) (some selected) maximum offset 1 positive disjoint
  have nextPresent : sourceReleased.nodeAt child = some returnNode := by
    change sourceReleased.nodes.get child = some returnNode
    rw [nodes]
    exact returnPresent
  have nextTagged : sourceReleased.indexOfTag returnTag = some child := by
    unfold BorrowTree.indexOfTag
    change sourceReleased.tagMapping.get returnTag = some child
    rw [mapping]
    exact returnTagged
  have nextHidden : S04ReturnReleaseParent.HiddenFrame sourceReleased borrowFrame := by
    intro row member index node present same
    apply hiddenFrame row member index node _ same
    change entry.allocation.extra.nodes.get index = some node
    change sourceReleased.nodes.get index = some node at present
    rw [nodes] at present
    exact present
  have nextDistinct : sourceReleased.roots.toList.Nodup := by rw [roots];exact distinct
  have nextOrder : ∀ valid : 0 < sourceReleased.roots.size,
      selected ≠ sourceReleased.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceReleased := by
    intro valid different
    have originalValid : 0 < entry.allocation.extra.roots.size := by rw [←roots];exact valid
    have originalDifferent : selected ≠ entry.allocation.extra.roots[0] := by simpa only [roots] using different
    have original := order originalValid originalDifferent
    simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,nodes] using original
  have nextShort : sourceReleased.nodes.size < 65536 := by rw [nodes];exact short
  have ownedReturn : (id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨returnDone,afterRuntime,parentPositive,_,_⟩ := S04ReturnReleaseParent.release_to_parent
    sourceReleased tracker.global borrowFrame afterSourceRuntime id returnTag child parent selected maximum offset
    afterSourcePositive returnNode nextPresent returnSame returnEdge returnHidden nextTagged ownedReturn nextHidden nextDistinct nextOrder nextShort activity
  let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
  have returnRelease : sourceReleased.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : sourceReleased.releaseProtector returnTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at returnDone
      cases returnDone
      simp only [released,h]
  have sourceRelease : entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags =
      ⟨sourceReleased,.Released⟩ := by
    cases h : entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags with
    | mk tree status =>
      simp only [h] at sourceDone
      cases sourceDone
      simp only [sourceReleased,h]
  have nextLive := StackPopRelease.lookup_commit_same machine.memory id entry sourceReleased
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (StackPopRelease.commitTree
        (StackPopRelease.commitTree machine.memory id entry sourceReleased)
        id {entry with allocation := entry.allocation.setExtra sourceReleased} released) := by
    rw [owned]
    exact .live id sourceTag entry sourceReleased [(id,returnTag)] machine.memory _
      live sourceRelease
      (.live id returnTag {entry with allocation := entry.allocation.setExtra sourceReleased} released [] _ _ nextLive returnRelease (.nil _))
  exact ⟨ActualPopPlan.pop_of_plan options limits remaining span frames frame machine tracker borrowFrame enabled
    frameTracked _ plan thread active,afterRuntime,parentPositive⟩

end
end DuplicatePrefix.S04ActiveSameReturnPop

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S04ActiveSameReturnPop.pop_after_source_activity) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved active same return pop dependency {dependency}"
