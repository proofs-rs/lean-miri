import duplicate_prefix.S05WriteCacheContributorOwnership

namespace DuplicatePrefix.S05ContributorCacheOrder
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open S05WriteCacheContributorOwnership
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Cache bounds only toward actual exposed Write contributors. Unsupported
children, including Disabled children, impose no raw-cache inequality. This is
an independent snapshot candidate; ordinary-call coverage remains unproved. -/
def ContributorOrder (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (support : UniIndex → Prop) : Prop :=
  ∀ query node, support query → tree.nodes.get query = some node →
    ∀ witness witnessNode, tree.nodes.get witness = some witnessNode →
      witnessNode.isExposed = true → query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).idempotentForeignAccess.rank ≤
        ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank

private theorem skip_cache (state : LocationState) (notDisabled : state.permission ≠ .Disabled)
    (skipped : skip state .Write .ForeignAccess = true) : state.idempotentForeignAccess = .Write := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases cache <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases cache <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]

private theorem retained (state : LocationState) (held : Bool)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held)
    (cached : state.idempotentForeignAccess = .Write) : losesWriteWhenForeign state.permission = false := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;> cases cache <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,Permission.strongestIdempotentForeignAccess,
        IdempotentForeignAccess.rank,losesWriteWhenForeign]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> cases cache <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,Permission.strongestIdempotentForeignAccess,
        IdempotentForeignAccess.rank,losesWriteWhenForeign]

/-- Contributor-only cache ordering suffices for the existing residual-pair
bridge. Unlike ParentCacheOrder, it permits low-cache Disabled children. -/
theorem skip_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (order : ContributorOrder tree location protections rights.area.contains)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (maximum : Option BorTag) : SkipStable tree location protections maximum rights.area.contains := by
  intro query node inside present skipped witness witnessNode found exposed walked supported
  have writable := rights.localRights query node inside present witness witnessNode found exposed walked .Write supported
  have queryCache := skip_cache _ writable.2.1 skipped
  have bound := order query node inside present witness witnessNode found exposed walked supported
  rw [queryCache] at bound
  have witnessCache : ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess = .Write := by
    cases value : ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess <;>
      simp_all [IdempotentForeignAccess.rank]
  have stable := retained _ (protections.contains witnessNode.tag) (profile.present witness witnessNode found) witnessCache
  simp only [removable,stable,Bool.and_false]

/-- State projection of the exact recording result, retaining the original
state on DebugAssertion. This projection does not treat errors as success. -/
def recordedForeignWrite (state : LocationState) : LocationState :=
  match state.recordNewAccess .Write .ForeignAccess with
  | .Recorded next => next
  | .DebugAssertion => state

/-- Foreign Write recording or its already-cached skip leaves every
non-Disabled node at Write cache strength. Disabled is the sole exception. -/
theorem record_write_cache (state : LocationState) (notDisabled : state.permission ≠ .Disabled) :
    (recordedForeignWrite state).idempotentForeignAccess = .Write := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases cache <;>
      simp_all [recordedForeignWrite,LocationState.recordNewAccess,LocationState.skipIfKnownNoop,
        AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen,
        IdempotentForeignAccess.recordNew,IdempotentForeignAccess.fromAccessAndRelatedness,
        IdempotentForeignAccess.max]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases cache <;>
      simp_all [recordedForeignWrite,LocationState.recordNewAccess,LocationState.skipIfKnownNoop,
        AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen,
        IdempotentForeignAccess.recordNew,IdempotentForeignAccess.fromAccessAndRelatedness,
        IdempotentForeignAccess.max]

/-- At an edge where both nodes receive a foreign Write, the contributor
bound is restored even without assuming initial order. Whole-visitor coverage
still must account for local/Either callbacks and skipped subtrees. -/
theorem foreign_write_bound (parent child : LocationState) (notDisabled : child.permission ≠ .Disabled) :
    (recordedForeignWrite parent).idempotentForeignAccess.rank ≤
      (recordedForeignWrite child).idempotentForeignAccess.rank := by
  rw [record_write_cache child notDisabled]
  cases value : (recordedForeignWrite parent).idempotentForeignAccess <;>
    decide +kernel

/-- The exact permission/protector stage preserves the recorded cache on all
outcomes, including errors; this is a metadata statement, not safety. -/
theorem perform_access_cache (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) :
    (state.performAccess kind related held).resultingState.idempotentForeignAccess =
      state.idempotentForeignAccess := by
  unfold LocationState.performAccess
  split
  · rfl
  · rfl
  · split
    · rfl
    · dsimp only
      split
      · rfl
      · split <;> rfl

/-- Recording followed by the actual permission stage preserves the
contributor bound; no successful transition or final safety is assumed. -/
theorem foreign_write_transition_bound (parent child : LocationState)
    (parentHeld childHeld : Bool) (notDisabled : child.permission ≠ .Disabled) :
    ((recordedForeignWrite parent).performAccess .Write .ForeignAccess parentHeld).resultingState.idempotentForeignAccess.rank ≤
      ((recordedForeignWrite child).performAccess .Write .ForeignAccess childHeld).resultingState.idempotentForeignAccess.rank := by
  rw [perform_access_cache,perform_access_cache]
  exact foreign_write_bound parent child notDisabled

end DuplicatePrefix.S05ContributorCacheOrder
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05ContributorCacheOrder.skip_stable,
      ``DuplicatePrefix.S05ContributorCacheOrder.record_write_cache,
      ``DuplicatePrefix.S05ContributorCacheOrder.foreign_write_bound,
      ``DuplicatePrefix.S05ContributorCacheOrder.perform_access_cache,
      ``DuplicatePrefix.S05ContributorCacheOrder.foreign_write_transition_bound] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
