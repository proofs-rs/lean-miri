import duplicate_prefix.S05ContributorCacheOrder
import duplicate_prefix.GeneralBorrowExposureMarkGraph
import duplicate_prefix.GeneralBorrowLocationUpdateFrame

namespace DuplicatePrefix.S05PotentialContributorExposure
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposureMarkGraph
open GeneralBorrowExposureRelease GeneralBorrowExposureMapFrame GeneralRangeMapState
open S05ContributorCacheOrder
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert

/-- Cache ordering toward all potential Write contributors, including currently
unexposed nodes. exposeTag changes exposure and counters without repairing SIFA,
so a relation stable under exposure must account for these latent supporters.
This source-motivated candidate is not declared ordinary-call validity. -/
def PotentialOrder (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) : Prop :=
  ∀ query node, support query → tree.nodes.get query = some node →
    ∀ witness witnessNode, tree.nodes.get witness = some witnessNode →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).idempotentForeignAccess.rank ≤
        ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank

theorem contributor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (order : PotentialOrder tree location protections support) :
    ContributorOrder tree location protections support := by
  intro query node inside present witness witnessNode found _ walked supported
  exact order query node inside present witness witnessNode found walked supported

private theorem nodes (before after : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) (same : after.nodes = before.nodes)
    (order : PotentialOrder before location protections support) :
    PotentialOrder after location protections support := by
  simpa only [PotentialOrder,same] using order

private theorem perms (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) (same : after.perms = before.perms)
    (order : PotentialOrder tree before protections support) :
    PotentialOrder tree after protections support := by
  simpa only [PotentialOrder,effective,same] using order

private theorem mark_backward (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (query : UniIndex) (value : TreeNode)
    (found : (marked tree.nodes index node).get query = some value) :
    ∃ old, tree.nodes.get query = some old ∧ old.tag = value.tag ∧ old.defaultLocationState = value.defaultLocationState := by
  by_cases same : query = index
  · subst query
    rw [show (marked tree.nodes index node).get index = some {node with isExposed := true} from
      GeneralBorrowFreshLocation.get_same tree.nodes index _] at found
    cases found
    exact ⟨node,present,rfl,rfl⟩
  · rw [show (marked tree.nodes index node).get query = tree.nodes.get query from
      GeneralBorrowFreshLocation.get_other tree.nodes index query _ same] at found
    exact ⟨value,found,rfl,rfl⟩

/-- Exact exposure-flag marking preserves the potential relation because tags,
lazy states and every finite ancestor walk are unchanged. -/
theorem mark (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (order : PotentialOrder tree location protections support) :
    PotentialOrder {tree with nodes := marked tree.nodes index node} location protections support := by
  intro query queryNode inside queryPresent witness witnessNode witnessPresent walked supported
  obtain ⟨oldQuery,oldQueryPresent,_,queryDefault⟩ := mark_backward tree index node present query queryNode queryPresent
  obtain ⟨oldWitness,oldWitnessPresent,witnessTag,witnessDefault⟩ := mark_backward tree index node present witness witnessNode witnessPresent
  change query ∈ walk (marked tree.nodes index node) ((marked tree.nodes index node).size+1) witness at walked
  rw [GeneralBorrowExposureMarkGraph.size tree.nodes index node present,walk_mark tree.nodes index node present] at walked
  have originalSupport : supports (effective location protections witness oldWitness) .Write = true := by
    simpa only [effective,witnessTag,witnessDefault] using supported
  simpa only [queryDefault,witnessDefault] using
    order query oldQuery inside oldQueryPresent witness oldWitness oldWitnessPresent walked originalSupport

/-- Actual BorrowTree.new initializes the potential relation at every location,
including lazy states: its sole physical node makes every applicable pair
reflexive. This is a local initialization fact, not an arbitrary-history claim. -/
theorem allocation_at (tag : BorTag) (size : Size) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) :
    PotentialOrder (BorrowTree.new tag size) location protections support := by
  intro query node _ present witness witnessNode found _ _
  have queryBound := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag size).nodes query node present
  have witnessBound := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag size).nodes witness witnessNode found
  have nodeSize : (BorrowTree.new tag size).nodes.data.size = 1 := by
    simp [BorrowTree.new,UniValMap.insert,UniValMap.extendTo,Id.run,bind,pure]
    rfl
  rw [nodeSize] at queryBound witnessBound
  have same : query = witness := GeneralBorrowNodeUpdate.index_injective query witness (by omega)
  subst witness
  have sameNode := Option.some.inj (present.symm.trans found)
  subst witnessNode
  exact Nat.le_refl _

theorem allocation (tag : BorTag) (size : Size) (protections : ProtectedTags) (support : UniIndex → Prop) :
    Every (fun location => PotentialOrder (BorrowTree.new tag size) location protections support)
      (BorrowTree.new tag size).locations := by
  intro position valid
  exact allocation_at tag size _ protections support

/-- FULL actual exposeTag, including real per-range counter updates, preserves
potential ordering and supplies the exposed-contributor condition. Operation
completion is derived from graph depth; no exposure result is supplied. -/
theorem expose (tree : BorrowTree) (protections : ProtectedTags) (support : UniIndex → Prop)
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (initial : Every (fun location => PotentialOrder tree location protections support) tree.locations) :
    (tree.exposeTag protections tag).outcome = .ok () ∧
      Every (fun location => PotentialOrder (tree.exposeTag protections tag).tree location protections support)
        (tree.exposeTag protections tag).tree.locations ∧
      Every (fun location => ContributorOrder (tree.exposeTag protections tag).tree location protections support)
        (tree.exposeTag protections tag).tree.locations := by
  have phase : (tree.exposeTag protections tag).outcome = .ok () ∧
      Every (fun location => PotentialOrder (tree.exposeTag protections tag).tree location protections support)
        (tree.exposeTag protections tag).tree.locations := by
    cases exposed : node.isExposed with
    | true =>
      have actual : tree.exposeTag protections tag = ⟨tree,.ok ()⟩ := by
        simp [BorrowTree.exposeTag,tagged,present,exposed]
      rw [actual]
      exact ⟨rfl,initial⟩
    | false =>
      let markedTree := {tree with nodes := marked tree.nodes index node}
      let update : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit := fun location =>
        let state := (location.perms.get index).getD node.defaultLocationState
        let level := state.permission.strongestAllowedLocalAccess (protections.contains tag)
        let change := location.exposedCache.updateExposure markedTree.nodes index .None level
        ({location with exposedCache := change.cache},change.outcome.mapError BorrowTree.TreeMutationError.ExposedCache)
      have markedDepth := GeneralBorrowExposureMarkGraph.depth tree.nodes depth index node present
      have markedPresent : markedTree.nodes.get index = some {node with isExposed := true} := GeneralBorrowFreshLocation.get_same tree.nodes index _
      have start : Every (fun location => PotentialOrder markedTree location protections support) markedTree.locations := by
        intro position valid
        exact mark tree _ protections support index node present (initial position valid)
      have each : ∀ location,PotentialOrder markedTree location protections support →
          (update location).2 = .ok () ∧ PotentialOrder markedTree (update location).1 protections support := by
        intro location order
        have success := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache markedTree.nodes markedDepth index _ markedPresent
          .None (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess (protections.contains tag))
        refine ⟨?_,perms markedTree location (update location).1 protections support rfl order⟩
        change (location.exposedCache.updateExposure markedTree.nodes index .None _).outcome.mapError _ = .ok ()
        rw [success];rfl
      have all := GeneralBorrowLocationUpdateProperty.every markedTree update
        (fun location => PotentialOrder markedTree location protections support)
        (fun location => PotentialOrder markedTree location protections support) start each
      have graph := GeneralBorrowLocationUpdateFrame.nodes markedTree update
      have actual : tree.exposeTag protections tag = source_location_update markedTree update := by
        unfold BorrowTree.exposeTag
        simp only [tagged,present,exposed,Bool.false_eq_true,↓reduceIte,Id.run,pure]
        rfl
      rw [actual]
      refine ⟨all.1,?_⟩
      intro position valid
      exact nodes markedTree _ _ protections support graph (all.2 position valid)
  refine ⟨phase.1,phase.2,?_⟩
  intro position valid
  exact contributor _ _ protections support (phase.2 position valid)

end DuplicatePrefix.S05PotentialContributorExposure
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05PotentialContributorExposure.contributor,
      ``DuplicatePrefix.S05PotentialContributorExposure.mark,
      ``DuplicatePrefix.S05PotentialContributorExposure.expose,
      ``DuplicatePrefix.S05PotentialContributorExposure.allocation_at,
      ``DuplicatePrefix.S05PotentialContributorExposure.allocation] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
