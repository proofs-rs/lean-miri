import duplicate_prefix.S05LiveSubtreeCacheSoundness
import duplicate_prefix.GeneralBorrowProtectorExposureSifaProfile
namespace DuplicatePrefix.S05LiveSubtreeCacheExposure
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposureMarkGraph GeneralRangeMapState
open GeneralBorrowExposureRelease GeneralBorrowExposureMapFrame S05LiveSubtreeCacheSoundness
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert
private theorem nodes (before after : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) (same : after.nodes = before.nodes)
    (order : Soundness before location protections support) :
    Soundness after location protections support := by
  simpa only [Soundness,LiveCone,same] using order

private theorem perms (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) (same : after.perms = before.perms)
    (order : Soundness tree before protections support) :
    Soundness tree after protections support := by
  simpa only [Soundness,LiveCone,effective,same] using order

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

private theorem mark_forward (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (query : UniIndex) (value : TreeNode)
    (found : tree.nodes.get query = some value) :
    ∃ next,(marked tree.nodes index node).get query = some next ∧ value.defaultLocationState = next.defaultLocationState := by
  by_cases same : query = index
  · subst query
    have sameNode := Option.some.inj (present.symm.trans found)
    subst value
    exact ⟨_,GeneralBorrowFreshLocation.get_same tree.nodes index _,rfl⟩
  · exact ⟨value,(GeneralBorrowFreshLocation.get_other tree.nodes index query _ same).trans found,rfl⟩

/-- Flag-only exposure changes neither the live barrier cone nor its numeric
permission-table cache bounds, including latent and future-unprotected nodes. -/
theorem mark (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (sound : Soundness tree location protections support) :
    Soundness {tree with nodes := marked tree.nodes index node} location protections support := by
  intro query queryNode inside queryPresent witness witnessNode witnessPresent walked live
  obtain ⟨oldQuery,oldQueryPresent,_,queryDefault⟩ := mark_backward tree index node present query queryNode queryPresent
  obtain ⟨oldWitness,oldWitnessPresent,witnessTag,witnessDefault⟩ := mark_backward tree index node present witness witnessNode witnessPresent
  have paths : ∀ source,walk (marked tree.nodes index node) ((marked tree.nodes index node).size+1) source =
      walk tree.nodes (tree.nodes.size+1) source := by
    intro source
    rw [GeneralBorrowExposureMarkGraph.size tree.nodes index node present,walk_mark tree.nodes index node present]
  change query ∈ walk (marked tree.nodes index node) ((marked tree.nodes index node).size+1) witness at walked
  rw [paths witness] at walked
  have oldLive : LiveCone tree location query witness := by
    intro middle middleNode middlePresent queryWalk witnessWalk
    obtain ⟨next,nextPresent,sameDefault⟩ := mark_forward tree index node present middle middleNode middlePresent
    have barrier := live middle next nextPresent
    change (query ∈ walk (marked tree.nodes index node) ((marked tree.nodes index node).size+1) middle) →
      (middle ∈ walk (marked tree.nodes index node) ((marked tree.nodes index node).size+1) witness) → _ at barrier
    rw [paths middle,paths witness] at barrier
    simpa only [sameDefault] using barrier queryWalk witnessWalk
  simpa only [queryDefault,witnessDefault,witnessTag] using
    sound query oldQuery inside oldQueryPresent witness oldWitness oldWitnessPresent walked oldLive

/-- Full actual exposeTag preserves soundness through real counter updates. -/
theorem expose (tree : BorrowTree) (protections : ProtectedTags) (support : UniIndex → Prop)
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (initial : Every (fun location => Soundness tree location protections support) tree.locations) :
    (tree.exposeTag protections tag).outcome = .ok () ∧
      Every (fun location => Soundness (tree.exposeTag protections tag).tree location protections support)
        (tree.exposeTag protections tag).tree.locations := by
  have phase : (tree.exposeTag protections tag).outcome = .ok () ∧
      Every (fun location => Soundness (tree.exposeTag protections tag).tree location protections support)
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
      have start : Every (fun location => Soundness markedTree location protections support) markedTree.locations := by
        intro position valid
        exact mark tree _ protections support index node present (initial position valid)
      have each : ∀ location,Soundness markedTree location protections support →
          (update location).2 = .ok () ∧ Soundness markedTree (update location).1 protections support := by
        intro location order
        have success := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache markedTree.nodes markedDepth index _ markedPresent
          .None (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess (protections.contains tag))
        refine ⟨?_,perms markedTree location (update location).1 protections support rfl order⟩
        change (location.exposedCache.updateExposure markedTree.nodes index .None _).outcome.mapError _ = .ok ()
        rw [success];rfl
      have all := GeneralBorrowLocationUpdateProperty.every markedTree update
        (fun location => Soundness markedTree location protections support)
        (fun location => Soundness markedTree location protections support) start each
      have graph := GeneralBorrowLocationUpdateFrame.nodes markedTree update
      have actual : tree.exposeTag protections tag = source_location_update markedTree update := by
        unfold BorrowTree.exposeTag
        simp only [tagged,present,exposed,Bool.false_eq_true,↓reduceIte,Id.run,pure]
        rfl
      rw [actual]
      refine ⟨all.1,?_⟩
      intro position valid
      exact nodes markedTree _ _ protections support graph (all.2 position valid)
  exact phase


/-- Exact exposure-counter release phase plus actual protector deletion. The
preceding implicit access inside releaseProtector is a separate obligation. -/
theorem release_exposure (tree : BorrowTree) (protections : ProtectedTags) (support : UniIndex → Prop) (index : UniIndex) (node : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (initial : Every (fun location => Soundness tree location protections support) tree.locations) :
    (tree.updateExposureForProtectorRelease node.tag).outcome = .ok () ∧
    Every (fun location => Soundness (tree.updateExposureForProtectorRelease node.tag).tree location protections support)
      (tree.updateExposureForProtectorRelease node.tag).tree.locations ∧
    Every (fun location => Soundness (tree.updateExposureForProtectorRelease node.tag).tree location (protections.remove node.tag) support)
      (tree.updateExposureForProtectorRelease node.tag).tree.locations := by
  have phase : (tree.updateExposureForProtectorRelease node.tag).outcome = .ok () ∧
      Every (fun location => Soundness (tree.updateExposureForProtectorRelease node.tag).tree location protections support)
        (tree.updateExposureForProtectorRelease node.tag).tree.locations := by
    cases exposed : node.isExposed with
    | false =>
      have actual : tree.updateExposureForProtectorRelease node.tag = ⟨tree,.ok ()⟩ := by
        simp [BorrowTree.updateExposureForProtectorRelease,tagged,present,exposed]
      rw [actual]
      exact ⟨rfl,initial⟩
    | true =>
      let update := GeneralBorrowProtectorReleaseExposureCache.callback tree index node
      have each : ∀ location,Soundness tree location protections support →
          (update location).2 = .ok () ∧ Soundness tree (update location).1 protections support := by
        intro location good
        have cacheSuccess := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes depth index node present
          (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess true)
          (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess false)
        refine ⟨?_,perms tree location (update location).1 protections support rfl good⟩
        change (location.exposedCache.updateExposure tree.nodes index _ _).outcome.mapError _ = .ok ()
        rw [cacheSuccess];rfl
      have all := GeneralBorrowLocationUpdateProperty.every tree update
        (fun location => Soundness tree location protections support) (fun location => Soundness tree location protections support) initial each
      have graph := GeneralBorrowLocationUpdateFrame.nodes tree update
      have actual : tree.updateExposureForProtectorRelease node.tag = source_location_update tree update := by
        unfold BorrowTree.updateExposureForProtectorRelease
        simp only [tagged,present,exposed,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,pure]
        rfl
      rw [actual]
      refine ⟨all.1,?_⟩
      intro position valid
      exact nodes tree _ _ protections support graph (all.2 position valid)
  refine ⟨phase.1,phase.2,?_⟩
  intro position valid
  exact remove_protector _ _ protections support node.tag (phase.2 position valid)


end DuplicatePrefix.S05LiveSubtreeCacheExposure
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05LiveSubtreeCacheExposure.mark,
      ``DuplicatePrefix.S05LiveSubtreeCacheExposure.expose,
      ``DuplicatePrefix.S05LiveSubtreeCacheExposure.release_exposure] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
