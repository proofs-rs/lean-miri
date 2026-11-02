import duplicate_prefix.S05ContributorCacheOrder
import duplicate_prefix.GeneralBorrowNodeUpdate

namespace DuplicatePrefix.S05ContributorVisitorStep
open Miri Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open S05ContributorCacheOrder
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem supports_allows (level : WildcardAccessLevel) : supports level .Write = level.allows .Write := by
  cases level <;> rfl

/-- ContributorOrder ignores exposed-cache counters. Either callbacks and
cache-only exposure updates preserve it whenever the permission map is framed. -/
theorem permission_frame (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop)
    (same : after.perms = before.perms)
    (order : ContributorOrder tree before protections support) :
    ContributorOrder tree after protections support := by
  intro query node inside present witness witnessNode found exposed walked supported
  simp only [effective,same] at supported ⊢
  exact order query node inside present witness witnessNode found exposed walked supported

/-- The exact single-node permission-map write used by the wildcard callback.
The frontier premise concerns retained contributors, not residual masks or
operation outcomes: postorder children must already have adequate caches. -/
theorem write_preserves (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop)
    (index : UniIndex) (old next : LocationState)
    (stored : location.perms.get index = some old)
    (order : ContributorOrder tree location protections support)
    (increasing : old.idempotentForeignAccess.rank ≤ next.idempotentForeignAccess.rank)
    (shrinks : ∀ held, (next.permission.strongestAllowedLocalAccess held).allows .Write = true →
      (old.permission.strongestAllowedLocalAccess held).allows .Write = true)
    (frontier : ∀ witness witnessNode, tree.nodes.get witness = some witnessNode →
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
      simpa only [atIndex,witnessFrame,Option.getD_some] using frontier witness witnessNode found exposed walked oldSupport
    · simpa only [other query old next stored querySame,witnessFrame] using
        order query node inside present witness witnessNode found exposed walked oldSupport

/-- State retained by the actual foreign Write callback after recording and
permission checking. DebugAssertion retains the state already materialized by
the visitor; projecting that state does not classify the outcome as success. -/
def foreignWriteStep (state : LocationState) (held : Bool) : LocationState :=
  match state.recordNewAccess .Write .ForeignAccess with
  | .DebugAssertion => state
  | .Recorded recorded => (recorded.performAccess .Write .ForeignAccess held).resultingState

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
contributor order once the postorder frontier has been established. The
frontier is the remaining visitor-induction obligation, not call validity. -/
theorem foreign_write_preserves (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (old : LocationState) (stored : location.perms.get index = some old)
    (order : ContributorOrder tree location protections support)
    (frontier : ∀ witness witnessNode, tree.nodes.get witness = some witnessNode →
      witnessNode.isExposed = true → index ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      (foreignWriteStep old (protections.contains node.tag)).idempotentForeignAccess.rank ≤
        ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank) :
    ContributorOrder tree {location with perms := location.perms.insert index (foreignWriteStep old (protections.contains node.tag))} protections support := by
  apply write_preserves tree location protections support index old _ stored order
  · exact (foreign_facts old (protections.contains node.tag)).1
  · exact (foreign_facts old (protections.contains node.tag)).2
  · exact frontier

end DuplicatePrefix.S05ContributorVisitorStep
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05ContributorVisitorStep.permission_frame,
      ``DuplicatePrefix.S05ContributorVisitorStep.write_preserves,
      ``DuplicatePrefix.S05ContributorVisitorStep.foreign_write_preserves] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
