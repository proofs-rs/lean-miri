import duplicate_prefix.CurrentCallEmptyEntryLenZeroFactoryQueries
import duplicate_prefix.CurrentCallEmptyEntryLenZeroRootAuthorization
import duplicate_prefix.CurrentCallEmptyEntryLenZeroSelectedPath

namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroFactory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem not_below (completion : Completion) (child target : UniIndex)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠child)
    (different : target≠child) : ¬Below completion child target := by
  intro path
  have same : target=child := by
    clear different
    induction path with
    | refl => rfl
    | @step predecessor target edge path induction =>
      exact False.elim ((noIncoming target predecessor edge) induction)
  exact different same

private theorem old_path_back {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (root target : UniIndex)
    (old : TreeNode) (oldAt : tree.nodes.get target=some old)
    (path : Path input.after root target) : Path tree root target := by
  induction path generalizing old with
  | refl node present => exact .refl _ old oldAt
  | @step parent child earlier node present edge ih =>
    obtain ⟨next,nextAt,_,parentEq,_⟩ := S03EmptySharedFrame.old_node input child old oldAt
    have same : node=next := Option.some.inj (present.symm.trans nextAt)
    have oldEdge : old.parent=some parent := parentEq.symm.trans (same ▸ edge)
    obtain ⟨oldParent,oldParentAt,_⟩ := input.depth.parent child old oldAt parent oldEdge
    exact .step (ih oldParent oldParentAt) old oldAt oldEdge

/-- Transport the actual orphan write factory through its two empty Shared helpers. -/
theorem two_helpers {tree : BorrowTree} {completion : Completion} {protections : ProtectedTags}
    {source : UniIndex} {qTag tag1 tag2 : BorTag}
    (factory : CurrentCallEmptyEntryBool.OrphanWriteFactory tree completion protections source qTag)
    (first : EmptyForestSharedPool.Input tree qTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (firstParent : first.parent=factory.orphan) (secondParent : second.parent=first.index)
    (qNode : TreeNode) (qAt : tree.nodes.get factory.orphan=some qNode)
    (qHidden : qNode.isExposed=false) (qParentless : qNode.parent=none) (qLeaf : qNode.children=#[])
    (sourceNode middleSourceNode : TreeNode)
    (sourceAt : tree.nodes.get source=some sourceNode)
    (middleSourceAt : first.after.nodes.get source=some middleSourceNode)
    (noIncoming1 : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠first.index)
    (noIncoming2 : ∀ (query predecessor : UniIndex),(extend completion first.index first.parent).parents[query.toNat]?=some (some predecessor) → predecessor≠second.index)
    (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts second.after global)
    (sameFlags : global.protectedTags=protections) :
    Nonempty (CurrentCallEmptyEntryBool.OrphanWriteFactory second.after
      (extend (extend completion first.index first.parent) second.index second.parent) protections source qTag) := by
  have parentAt : tree.nodes.get factory.orphan=some first.parentNode := by simpa only [firstParent,BorrowTree.nodeAt] using first.present
  have parentNodeEq : first.parentNode=qNode := Option.some.inj (parentAt.symm.trans qAt)
  have parentless : first.parentNode.parent=none := parentNodeEq ▸ qParentless
  have roots := CurrentCallEmptyEntryLenZeroOldRootFrame.roots first second
  have selectedFrame := CurrentCallEmptyEntryLenZeroOldRootFrame.nodes first second secondParent parentless
    factory.selected factory.selected (by simpa only [firstParent] using factory.different)
    (.refl factory.selected factory.selectedNode factory.selectedAt)
  have ancestry (ancestor : UniIndex) :=
    (CurrentCallEmptyEntryLenZeroTransport.ancestry_iff first.after (extend completion first.index first.parent)
      tag1 tag2 second source middleSourceNode middleSourceAt noIncoming2 ancestor).trans
    (CurrentCallEmptyEntryLenZeroTransport.ancestry_iff tree completion qTag tag1 first source sourceNode sourceAt noIncoming1 ancestor)
  have noBelowQ := fun below => factory.notBelow ((ancestry factory.orphan).mp below)
  have noBelowFirst : ¬Below (extend (extend completion first.index first.parent) second.index second.parent) first.index source := by
    intro below
    have oldBelow := (ancestry first.index).mp below
    apply (not_below completion first.index source noIncoming1 ?_) oldBelow
    intro same
    rw [same,first.vacant] at sourceAt
    cases sourceAt

  have noBelowSecond : ¬Below (extend (extend completion first.index first.parent) second.index second.parent) second.index source := by
    intro below
    have oldBelow := (CurrentCallEmptyEntryLenZeroTransport.ancestry_iff first.after (extend completion first.index first.parent)
      tag1 tag2 second source middleSourceNode middleSourceAt noIncoming2 second.index).mp below
    apply (not_below _ second.index source noIncoming2 ?_) oldBelow
    intro same
    rw [same,second.vacant] at middleSourceAt
    cases middleSourceAt
  refine ⟨{ selectedPosition:=factory.selectedPosition, selected:=factory.selected, selectedNode:=factory.selectedNode
            selectedSlot:=by simpa only [roots] using factory.selectedSlot
            selectedAt:=selectedFrame.trans factory.selectedAt
            selectedPath:=CurrentCallEmptyEntryLenZeroOldRootFrame.paths first second _ _ factory.selectedPath
            orphan:=factory.orphan, orphanPosition:=factory.orphanPosition
            orphanMapped:=S03EmptySharedFrame.tagged second qTag factory.orphan (S03EmptySharedFrame.tagged first qTag factory.orphan factory.orphanMapped)
            orphanSlot:=by simpa only [roots] using factory.orphanSlot
            later:=factory.later, notBelow:=noBelowQ, different:=factory.different
            distinct:=by simpa only [roots] using factory.distinct
            selectedClassification:=by
              intro query node present path
              obtain ⟨old,oldAt,oldPath⟩ := CurrentCallEmptyEntryLenZeroSelectedPath.paths first second secondParent parentless
                factory.selected factory.selectedNode factory.selectedAt
                (by simpa only [firstParent] using factory.different) query path
              refine (ancestry query).trans ((factory.selectedClassification query old oldAt oldPath).trans ?_)
              constructor
              · exact CurrentCallEmptyEntryLenZeroOldRootFrame.paths first second query source
              · intro afterPath
                exact old_path_back first query source sourceNode sourceAt
                  (old_path_back second query source middleSourceNode middleSourceAt afterPath)
            callbacks:=?_ }⟩
  intro current authority position root rootSlot notSelected consistent
  have oldSlot : tree.roots[position]?=some root := by simpa only [roots] using rootSlot
  by_cases same : root=factory.orphan
  · subst root
    have positionEq : position=factory.orphanPosition := by
      have bound : position<tree.roots.size := by
        by_cases h : position<tree.roots.size
        · exact h
        · have missing := Array.getElem?_eq_none (by omega : tree.roots.size≤position)
          rw [missing] at oldSlot
          cases oldSlot
      apply (factory.distinct.getElem?_inj (by simpa using bound)).mp
      simpa using oldSlot.trans factory.orphanSlot.symm
    have later : 0<position := positionEq ▸ factory.later
    let depth := Classical.choice runtime.formed.depth
    obtain ⟨forest⟩ := runtime.formed.forest current global.protectedTags
    have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest second.after current global.protectedTags forest depth
    have noBelow (query : UniIndex) (path : Path second.after factory.orphan query) :
        ¬Below (extend (extend completion first.index first.parent) second.index second.parent) query source := by
      rcases CurrentCallEmptyEntryLenZeroRootAuthorization.qPath_cases first second factory.orphan qNode qAt
        qHidden qParentless qLeaf firstParent secondParent reciprocal query path with same | same | same
      · exact same ▸ noBelowQ
      · exact same ▸ noBelowFirst
      · exact same ▸ noBelowSecond
    obtain ⟨auth,relation⟩ := CurrentCallEmptyEntryLenZeroRootAuthorization.two_helpers_consistent first second factory.orphan qNode qAt
      qHidden qParentless qLeaf firstParent secondParent global runtime position rootSlot later (some factory.selectedNode.tag) current
      (by simpa only [sameFlags] using consistent)
      (by intro index node present path;simpa only [sameFlags] using (authority index node present).2 (noBelow index path))
    refine ⟨⟨fun query=>Path second.after factory.orphan query,by simpa only [sameFlags] using auth,fun _ path=>path,?_⟩⟩
    intro removed _ query node path present
    exact ⟨fun below=>False.elim (noBelow query path below),fun _=>Or.inl (by simpa only [sameFlags] using relation removed query node path present)⟩
  · exact CurrentCallEmptyEntryLenZeroFactoryQueries.old_queries factory first second firstParent secondParent parentless
      noIncoming1 noIncoming2 sourceNode middleSourceNode sourceAt middleSourceAt current authority position root oldSlot notSelected same consistent

end
end DuplicatePrefix.CurrentCallEmptyEntryLenZeroFactory

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroFactory" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual len-zero factory dependency {dependency}"
