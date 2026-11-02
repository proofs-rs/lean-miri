import duplicate_prefix.S05SemanticReadEffects

namespace DuplicatePrefix.S05SemanticReadSoundnessStep
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureAncestorFold GeneralBorrowSifaPermissionConsistency
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open S05LiveSubtreeCacheSoundness S05SemanticReadEffects
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert

private theorem weaken_cache (state : LocationState) (held : Bool) (before after : IdempotentForeignAccess)
    (bound : Consistent {state with idempotentForeignAccess := before} held)
    (smaller : after.rank ≤ before.rank) : Consistent {state with idempotentForeignAccess := after} held := by
  obtain ⟨strength,table,large⟩ := bound
  exact ⟨strength,table,Nat.le_trans smaller large⟩

/-- Exact Read effects transport semantic soundness whenever query caches do
not grow. This covers Local callbacks and Either materialization, including
all unexposed descendants and protector-dependent permission tables. -/
theorem nongrowing (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (sound : Soundness tree before protections support)
    (effects : Effects tree before after protections)
    (caches : ∀ query node,support query → tree.nodes.get query = some node →
      (effective after query node).idempotentForeignAccess.rank ≤ (effective before query node).idempotentForeignAccess.rank) :
    Soundness tree after protections support := by
  intro query node inside present witness witnessNode found walked live
  have oldLive := live_backward tree before after protections effects query witness live
  have bound := sound query node inside present witness witnessNode found walked oldLive
  have moved := transport _ _ _ _ (effects witness witnessNode found) bound
  exact weaken_cache _ _ _ _ moved (caches query node inside present)

theorem either_post (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (sound : Soundness tree location protections support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    Soundness tree (materialized location index node) protections support := by
  apply nongrowing tree location _ protections support sound
    (S05SemanticReadEffects.materialize tree location location protections (S05SemanticReadEffects.initial tree location protections) index node present)
  intro query queryNode inside found
  rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree location index node present query queryNode found]
  exact Nat.le_refl _

private theorem local_record_cache (state recorded : LocationState)
    (record : state.recordNewAccess .Read .LocalAccess = .Recorded recorded) : recorded.idempotentForeignAccess = .None := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

/-- Actual source Local Read callback mutation preserves Soundness. Success
is an internal scalar equation supplied by the DFS-derived action. -/
theorem local_post (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (sound : Soundness tree location protections support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (recorded next : LocationState) (delta : PermTransition)
    (record : (effective location index node).recordNewAccess .Read .LocalAccess = .Recorded recorded)
    (access : recorded.performAccess .Read .LocalAccess (protections.contains node.tag) = .Success next delta) :
    Soundness tree (updated tree location index node protections recorded next delta) protections support := by
  have effects := S05SemanticReadEffects.update tree location location protections
    (S05SemanticReadEffects.initial tree location protections) index node present recorded next delta .LocalAccess record access
  have cache := S05ContributorCacheOrder.perform_access_cache recorded .Read .LocalAccess (protections.contains node.tag)
  rw [access] at cache
  simp only [LocationState.AccessResult.resultingState,local_record_cache _ _ record] at cache
  apply nongrowing tree location _ protections support sound effects
  intro query queryNode inside found
  by_cases same : query = index
  · subst query
    have nodeEq := Option.some.inj (present.symm.trans found)
    subst queryNode
    simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some,cache,IdempotentForeignAccess.rank]
    exact Nat.zero_le _
  · rw [effective,updated_other tree location index query node protections recorded next delta same]
    exact Nat.le_refl _

/-- Foreign Read cache gain is sound once the actual child-first frontier has
established numeric Read idempotence at every strict live descendant. No
relation between descendant cached values is required. -/
theorem foreign_post (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (sound : Soundness tree location protections support)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (recorded next : LocationState) (delta : PermTransition)
    (record : (effective location index node).recordNewAccess .Read .ForeignAccess = .Recorded recorded)
    (access : recorded.performAccess .Read .ForeignAccess (protections.contains node.tag) = .Success next delta)
    (frontier : ∀ witness witnessNode,witness ≠ index → tree.nodes.get witness = some witnessNode →
      index ∈ walk tree.nodes (tree.nodes.size+1) witness →
      LiveCone tree (updated tree location index node protections recorded next delta) index witness →
      Consistent {effective (updated tree location index node protections recorded next delta) witness witnessNode with
        idempotentForeignAccess := next.idempotentForeignAccess} (protections.contains witnessNode.tag)) :
    Soundness tree (updated tree location index node protections recorded next delta) protections support := by
  have effects := S05SemanticReadEffects.update tree location location protections
    (S05SemanticReadEffects.initial tree location protections) index node present recorded next delta .ForeignAccess record access
  intro query queryNode inside queryPresent witness witnessNode found walked live
  by_cases querySame : query = index
  · subst query
    have nodeEq := Option.some.inj (present.symm.trans queryPresent)
    subst queryNode
    by_cases witnessSame : witness = index
    · subst witness
      have witnessEq := Option.some.inj (present.symm.trans found)
      subst witnessNode
      have oldLive := live_backward tree location _ protections effects index index live
      have own := sound index node inside present index node present walked oldLive
      have good := GeneralBorrowSifaPermissionConsistency.pipeline (effective location index node) recorded next delta .Read .ForeignAccess
        (protections.contains node.tag) own record access
      simpa only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using good
    · simpa only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using
        frontier witness witnessNode witnessSame found walked live
  · have oldLive := live_backward tree location _ protections effects query witness live
    have own := sound query queryNode inside queryPresent witness witnessNode found walked oldLive
    have moved := transport _ _ _ _ (effects witness witnessNode found) own
    simpa only [effective,updated_other tree location index query node protections recorded next delta querySame] using moved

end DuplicatePrefix.S05SemanticReadSoundnessStep
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05SemanticReadSoundnessStep.nongrowing,
      ``DuplicatePrefix.S05SemanticReadSoundnessStep.either_post,
      ``DuplicatePrefix.S05SemanticReadSoundnessStep.local_post,
      ``DuplicatePrefix.S05SemanticReadSoundnessStep.foreign_post] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
