import duplicate_prefix.GeneralBorrowProtectedEntryNext
import duplicate_prefix.GeneralBorrowForestMutableCleanRange
namespace DuplicatePrefix.GeneralBorrowProtectedEntryActivate
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual current-child Write preserves the complete next-entry factory,
including vacant permission cleanliness and retained active protectors. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (parentTag nextTag : BorTag)
    (offset len : UInt64) (s : GeneralBorrowForestDefaultStageNext.Output tree protections parentTag nextTag offset len)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let actual := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
    actual.status=.Completed ∧
      Nonempty (GeneralBorrowForestDefaultStageNext.Output actual.tree protections parentTag nextTag offset len) ∧
      actual.tree.locations.size=tree.locations.size := by
  let actual := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
  let after := actual.tree
  let d := s.data
  have ran := GeneralBorrowForestMutableSlice.access tree protections parentTag d.parent d.primary d.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Write .VisitChildrenOfAccessed d.context d.tagPresent d.well d.nodeFits offset (offset+len)
    d.owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame : after={tree with locations:=after.locations} := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag)
    (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
  have nodes : after.nodes=tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : after.tagMapping=tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree after nodes d.context.depth
  let context : GeneralBorrowForestAccessData.Context after d.parent d.primary d.extras := {
    anchorNode:=d.context.anchorNode,primaryNode:=d.context.primaryNode,depth:=depth,
    children:=by rw [frame];exact d.context.children,
    anchorPresent:=by change after.nodes.get d.parent=_;rw [nodes];exact d.context.anchorPresent,
    primaryPresent:=by rw [nodes];exact d.context.primaryPresent,
    roots:=by rw [frame];exact d.context.roots,different:=d.context.different,
    unexposed:=by intro index node present;rw [nodes] at present;exact d.context.unexposed index node present }
  let slot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree after d.context.depth depth nodes mapping rfl d.parent d.slot
  have clean : GeneralBorrowGcVacantClean.VacantClean after := by
    intro query vacant
    have old : tree.nodes.get query=none := by rw [←nodes];exact vacant
    exact (GeneralBorrowForestMutableCleanRange.ranged tree protections parentTag d.parent d.primary query d.extras
      (Size.ofBytes offset) (Size.ofBytes len) .Write .VisitChildrenOfAccessed d.context d.nodeFits d.tagPresent old (s.vacantClean query old)
      d.well offset (offset+len) d.owned bounds (Nat.le_refl _) (Nat.le_refl _)).2
  let allocator : GeneralBorrowGcAllocator.Invariant after := by
    rw [frame]
    exact ⟨s.allocator.pool,s.allocator.accounting,s.allocator.unique,s.allocator.nodeTags⟩
  let data : GeneralBorrowForestEntryValidity.Data after protections parentTag nextTag offset len := {
    parent:=d.parent,primary:=d.primary,extras:=d.extras,context:=context,
    covered:=by rw [frame];exact d.covered,tagPresent:=by change after.tagMapping.get parentTag=_;rw [mapping];exact d.tagPresent,
    tagFresh:=by rw [mapping];exact d.tagFresh,globalUnheld:=d.globalUnheld,nodeTags:=allocator.nodeTags,
    nodeFits:=by rw [nodes];exact d.nodeFits,slot:=slot,well:=ran.2.2.1,owned:=ran.2.1 }
  refine ⟨ran.1,⟨⟨data,?_,allocator,clean⟩⟩,ran.2.2.2⟩
  apply clean
  have vacant := GeneralBorrowFreshSharedWithinStages.slot_vacant after depth d.parent slot
  cases slot <;> exact vacant
end
end DuplicatePrefix.GeneralBorrowProtectedEntryActivate
