import duplicate_prefix.S05WriteCacheContributorOwnership

namespace DuplicatePrefix.S05RawCacheOrderMutationGap
open Miri Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false

/-- Two individually consistent scalar states whose raw caches are ordered.
The child is already disabled, so foreign accesses may skip it without recording
an access. These are scalar data, not a claim about Rust-call reachability. -/
def parentState : LocationState := ⟨.Cell, true, .None⟩
def childState : LocationState := ⟨.Disabled, true, .None⟩
def recordedParent : LocationState := ⟨.Cell, true, .Write⟩

theorem initial_consistent :
    GeneralBorrowSifaPermissionConsistency.Consistent parentState false ∧
    GeneralBorrowSifaPermissionConsistency.Consistent childState false := by
  exact ⟨⟨.Write, rfl, by decide +kernel⟩, ⟨.Write, rfl, by decide +kernel⟩⟩

theorem initially_ordered :
    parentState.idempotentForeignAccess.rank ≤ childState.idempotentForeignAccess.rank := by
  decide +kernel

/-- The actual parent recording operation strengthens its cache. No operation
success is assumed: its exact result is proved from the initial scalar data. -/
theorem parent_records :
    parentState.recordNewAccess .Write .ForeignAccess = .Recorded recordedParent := by
  decide +kernel

/-- The actual child skip predicate prevents both recording and traversal.
This is the interpreter's Disabled optimization, independent of its raw SIFA. -/
theorem child_skips :
    childState.skipIfKnownNoop .Write .ForeignAccess = .SkipSelfAndChildren := by
  decide +kernel

theorem parent_access :
    recordedParent.performAccess .Write .ForeignAccess false =
      .Success recordedParent ⟨.Cell, .Cell⟩ := by
  decide +kernel

/-- The skipped low-cache child cannot contribute Write support. Thus this
raw-order failure is harmless for the contributor-based SkipStable condition;
coverage should permit this state rather than demanding raw cache order. -/
theorem child_no_write_support (held : Bool) :
    (childState.permission.strongestAllowedLocalAccess held).allows .Write = false := by
  cases held <;> decide +kernel

theorem afterwards_consistent :
    GeneralBorrowSifaPermissionConsistency.Consistent recordedParent false ∧
    GeneralBorrowSifaPermissionConsistency.Consistent childState false := by
  exact ⟨⟨.Write, rfl, by decide +kernel⟩, ⟨.Write, rfl, by decide +kernel⟩⟩

/-- Consequently a raw-cache ordering invariant cannot be preserved merely
by saying that foreign accesses strengthen both caches: the child is skipped.
This local mutation obstruction does not refute semantic subtree idempotence,
SkipStable, or establish a reachable ordinary Rust call counterexample. -/
theorem afterwards_unordered :
    ¬ recordedParent.idempotentForeignAccess.rank ≤ childState.idempotentForeignAccess.rank := by
  decide +kernel

end DuplicatePrefix.S05RawCacheOrderMutationGap
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05RawCacheOrderMutationGap.initial_consistent,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.initially_ordered,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.parent_records,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.child_skips,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.parent_access,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.afterwards_unordered,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.child_no_write_support,
      ``DuplicatePrefix.S05RawCacheOrderMutationGap.afterwards_consistent] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
