import duplicate_prefix.S05ContributorVisitorStep

namespace DuplicatePrefix.S05ContributorPostorderFrontier
open Miri Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open S05ContributorCacheOrder
open S05ContributorVisitorStep (foreignWriteStep)
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem supports_allows (level : WildcardAccessLevel) : supports level .Write = level.allows .Write := by
  cases level <;> rfl

/-- The exact single-node permission-map write used by the wildcard callback.
The frontier premise concerns retained contributors, not residual masks or
operation outcomes: strict postorder descendants must already have adequate caches. The updated
node itself is excluded: its new reflexive cache bound holds automatically. -/
theorem write_preserves (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop)
    (index : UniIndex) (old next : LocationState)
    (stored : location.perms.get index = some old)
    (order : ContributorOrder tree location protections support)
    (increasing : old.idempotentForeignAccess.rank ≤ next.idempotentForeignAccess.rank)
    (shrinks : ∀ held, (next.permission.strongestAllowedLocalAccess held).allows .Write = true →
      (old.permission.strongestAllowedLocalAccess held).allows .Write = true)
    (frontier : ∀ witness witnessNode, witness ≠ index → tree.nodes.get witness = some witnessNode →
      witnessNode.isExposed = true → index ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      next.idempotentForeignAccess.rank ≤
        ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank) :
    ContributorOrder tree {location with perms := location.perms.insert index next} protections support := by
  have atIndex := GeneralBorrowNodeUpdate.insert_existing_get_same location.perms index old next stored
  have other := GeneralBorrowNodeUpdate.insert_existing_get_other location.perms index
  intro query node inside present witness witnessNode found exposed walked supported
  by_cases witnessSame : witness = index
  · subst witness
    simp only [effective,atIndex,Option.getD_some] at supported
    have oldSupport : supports (effective location protections index witnessNode) .Write = true := by
      rw [supports_allows] at supported
      change (next.permission.strongestAllowedLocalAccess (protections.contains witnessNode.tag)).allows .Write = true at supported
      simp only [effective,stored,Option.getD_some]
      rw [supports_allows]
      change (old.permission.strongestAllowedLocalAccess (protections.contains witnessNode.tag)).allows .Write = true
      exact shrinks _ supported
    have bound := order query node inside present index witnessNode found exposed walked oldSupport
    simp only [stored,Option.getD_some] at bound
    by_cases querySame : query = index
    · subst query
      simp only [atIndex,Option.getD_some]
      exact Nat.le_refl _
    · simpa only [other query old next stored querySame,atIndex,stored,Option.getD_some] using Nat.le_trans bound increasing
  · have witnessFrame := other witness old next stored witnessSame
    have oldSupport : supports (effective location protections witness witnessNode) .Write = true := by
      simpa only [effective,witnessFrame] using supported
    by_cases querySame : query = index
    · subst query
      simpa only [atIndex,witnessFrame,Option.getD_some] using frontier witness witnessNode witnessSame found exposed walked oldSupport
    · simpa only [other query old next stored querySame,witnessFrame] using
        order query node inside present witness witnessNode found exposed walked oldSupport

private theorem foreign_facts (state : LocationState) (actual : Bool) :
    state.idempotentForeignAccess.rank ≤ (foreignWriteStep state actual).idempotentForeignAccess.rank ∧
    (∀ held, ((foreignWriteStep state actual).permission.strongestAllowedLocalAccess held).allows .Write = true →
      (state.permission.strongestAllowedLocalAccess held).allows .Write = true) := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases cache <;> cases actual <;>
      constructor <;> first | decide +kernel | intro held; cases held <;> decide +kernel
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases cache <;> cases actual <;>
      constructor <;> first | decide +kernel | intro held; cases held <;> decide +kernel

/-- Actual foreign callback mutation, including permission errors, preserves
contributor order once the strict postorder frontier has been established. The
frontier is the remaining visitor-induction obligation, not call validity. -/
theorem foreign_write_preserves (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (old : LocationState) (stored : location.perms.get index = some old)
    (order : ContributorOrder tree location protections support)
    (frontier : ∀ witness witnessNode, witness ≠ index → tree.nodes.get witness = some witnessNode →
      witnessNode.isExposed = true → index ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      (foreignWriteStep old (protections.contains node.tag)).idempotentForeignAccess.rank ≤
        ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank) :
    ContributorOrder tree {location with perms := location.perms.insert index (foreignWriteStep old (protections.contains node.tag))} protections support := by
  apply write_preserves tree location protections support index old _ stored order
  · exact (foreign_facts old (protections.contains node.tag)).1
  · exact (foreign_facts old (protections.contains node.tag)).2
  · exact frontier

end DuplicatePrefix.S05ContributorPostorderFrontier
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05ContributorPostorderFrontier.write_preserves,
      ``DuplicatePrefix.S05ContributorPostorderFrontier.foreign_write_preserves] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
