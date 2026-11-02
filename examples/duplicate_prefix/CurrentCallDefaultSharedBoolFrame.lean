import duplicate_prefix.S05SharedConstructorDisjoint
import duplicate_prefix.CurrentCallReadRootActivity
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.GeneralBorrowRawSharedExpression
import duplicate_prefix.CandidateCurrentJointRawReplacement
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime

namespace DuplicatePrefix.CurrentCallDefaultSharedBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05ConcreteProtectedChildCompletion GeneralBorrowRawSharedExpression
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Default shared-reference allocation, its actual associated Read, and its
actual Frozen constructor preserve the current Bool child's disjoint authority
and exact hidden-leaf/activity facets. Both real allocator choices are covered. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (position : Nat) (selected parent target : UniIndex) (selectedNode parentNode targetNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode) (parentPath : Path tree selected parent)
    (targetAt : tree.nodeAt target = some targetNode) (targetLeaf : targetNode.children = #[])
    (targetHidden : targetNode.isExposed = false) (different : target ≠ parent)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations)
    (targetOwned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let advanced := GeneralBorrowFnEntryRegistration.advanced global room
    let accessed := read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
    let actual := child tree advanced.protectedTags parentNode.tag global.nextPointerTag offset len .VisitChildrenOfAccessed
    accessed.status = .Completed ∧ actual.outcome = .ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts actual.tree advanced ∧ actual.tree.locations.size = tree.locations.size ∧
    actual.tree.nodes.size ≤ tree.nodes.size+1 ∧ ∃ freshChild,
      actual.tree.indexOfTag global.nextPointerTag = some freshChild ∧
      OwnedOn (Authority actual.tree (extend completion freshChild parent) advanced.protectedTags target) lower upper actual.tree.locations ∧
      (∃ next, actual.tree.nodeAt target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
        next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write lower upper := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global room
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced = allocated := congrArg Prod.fst
    (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have current : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,by
      simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false,advanced,GeneralBorrowFnEntryRegistration.advanced] using below⟩
  obtain ⟨depth⟩ := current.formed.depth
  have rows : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      S05CompletedAncestryReadMutable.Authority tree completion advanced.protectedTags parent location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨current.possible cursor valid,owned cursor valid positive start stop⟩
  have accessed := S05CompletedAncestryReadMutable.range tree completion advanced.protectedTags complete
    current.formed.toGraphState depth order position selected parent selectedNode parentNode slot selectedPresent parentPresent parentPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows current.formed.well
    (fun cursor valid => ⟨current.coherent cursor valid,current.formed.profile cursor valid,current.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  let after := read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
  have same : after.tree = {tree with locations := after.tree.locations} := accessed.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts after.tree advanced := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ current.formed.toGraphState,accessed.well⟩,?_⟩,
      ?_,?_,⟨current.below.mapping,current.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(accessed.runtime cursor valid).2.1.present,(accessed.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid; exact (accessed.runtime cursor valid).1
    · intro cursor valid; exact (accessed.runtime cursor valid).2.2
  have tagged : after.tree.indexOfTag parentNode.tag = some parent := by
    unfold BorrowTree.indexOfTag
    change (tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed).tree.tagMapping.get parentNode.tag = _
    rw [accessed.tags]
    exact (complete.2.2.2.2.1 parent parentNode parentPresent).1
  have present : after.tree.nodeAt parent = some parentNode := by
    change after.tree.nodes.get parent = some parentNode
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using parentPresent
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping global.nextPointerTag := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.tags] using fresh
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have afterComplete : Completes after.tree completion := by
    rw [same]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  have afterOwned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority after.tree completion advanced.protectedTags parent)
      offset (offset+len) after.tree.locations := by
    intro cursor valid positive start stop index node nodeAt
    have authority := (accessed.rows cursor valid positive start stop).2
    exact authority index node (by simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using nodeAt)
  have nodeRoomAfter : after.tree.nodes.size+1 ≤ 4294967295 := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ after.tree.locations.size.bytes.toNat := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.capacity] using bounds
  have targetOwnedAfter : OwnedOn (Authority after.tree completion advanced.protectedTags target) lower upper after.tree.locations := by
    have retained := GeneralBorrowRangeOutsideOwned.owned (Authority tree completion advanced.protectedTags target)
      tree (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed
      current.formed.well bounds lower upper disjoint targetOwned
    intro cursor valid positive start stop index node nodeAt
    exact retained cursor valid positive start stop index node (by simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using nodeAt)
  have targetAfter : after.tree.nodeAt target = some targetNode := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,BorrowTree.nodeAt,accessed.nodes] using targetAt
  have readNormalRows : OwnedOn (fun location => Nonempty
      (DuplicatePrefixNormalKind.Capability tree location advanced.protectedTags parent .Read)) offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    have authority := owned cursor valid positive start stop
    obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion _ advanced.protectedTags complete
      current.formed.toGraphState depth current.formed.fits position selected parent selectedNode slot selectedPresent parentPath
      (fun index node found _ => (authority index node found).1)
      (fun index node found _ => (authority index node found).2)
    exact ⟨DuplicatePrefixNormalKind.of_normal tree _ advanced.protectedTags parent normal .Read⟩
  have targetActiveAfter : GeneralBorrowFreshActiveWithin.ActiveWithin after.tree target .Write lower upper :=
    CurrentCallReadRootActivity.concrete_of_normal tree advanced current parentNode.tag parent target parentNode parentPresent
      offset len bounds readNormalRows ((complete.2.2.2.2.1 parent parentNode parentPresent).1)
      targetNode targetAt targetLeaf targetHidden different lower upper targetActive .VisitChildrenOfAccessed
  obtain ⟨done,resultRuntime,capacity,growth,freshChild,lookup,retained⟩ := S05SharedConstructorDisjoint.construct after.tree advanced completion
    afterRuntime afterComplete parentNode.tag global.nextPointerTag parent target parentNode targetNode tagged present targetAfter freshAfter nodeRoomAfter
    tagBound false unheld offset len lower upper nonzero boundsAfter disjoint targetOwnedAfter
  have facets := S05SharedConstructorDisjoint.old_facets after.tree advanced afterRuntime parentNode.tag global.nextPointerTag
    parent target parentNode targetNode tagged present targetAfter different freshAfter nodeRoomAfter false offset len nonzero boundsAfter
    .Write lower upper targetActiveAfter
  refine ⟨accessed.completed,done,resultRuntime,capacity.trans accessed.capacity,?_,freshChild,lookup,retained,facets⟩
  simpa only [after,advanced,GeneralBorrowRawSharedExpression.child,GeneralBorrowRawSharedExpression.read,accessed.nodes] using growth

end DuplicatePrefix.CurrentCallDefaultSharedBoolFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallDefaultSharedBoolFrame").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved default shared Bool frame dependency {dependency}"
