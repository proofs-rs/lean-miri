import duplicate_prefix.S05NoCutoffOwnershipBridge
import duplicate_prefix.GeneralBorrowSifaPermissionConsistency
import duplicate_prefix.GeneralBorrowLocationSifaConsistency

namespace DuplicatePrefix.S05WriteCacheContributorOwnership
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Call-time cache ordering on physical parent edges. This is initial data,
not successful traversal or a residual-query assumption. Its ordinary-history
formation is a separate obligation; scalar SIFA bounds alone do not imply it. -/
def ParentCacheOrder (tree : BorrowTree) (location : LocationTree) : Prop :=
  ∀ child childNode,tree.nodes.get child = some childNode → ∀ parent parentNode,
    childNode.parent = some parent → tree.nodes.get parent = some parentNode →
      ((location.perms.get parent).getD parentNode.defaultLocationState).idempotentForeignAccess.rank ≤
      ((location.perms.get child).getD childNode.defaultLocationState).idempotentForeignAccess.rank

theorem path_cache_le (tree : BorrowTree) (location : LocationTree) (order : ParentCacheOrder tree location)
    (root witness : UniIndex) (path : Path tree root witness)
    (rootNode witnessNode : TreeNode) (rootPresent : tree.nodes.get root = some rootNode)
    (witnessPresent : tree.nodes.get witness = some witnessNode) :
    ((location.perms.get root).getD rootNode.defaultLocationState).idempotentForeignAccess.rank ≤
      ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank := by
  induction path generalizing witnessNode with
  | refl node present =>
    have first := Option.some.inj (rootPresent.symm.trans present)
    have last := Option.some.inj (witnessPresent.symm.trans present)
    simp only [first,last]
    exact Nat.le_refl _
  | @step parent child earlier node present edge ih =>
    obtain ⟨parentNode,parentPresent⟩ := earlier.present
    have before := ih parentNode parentPresent
    have after := order child node present parent parentNode edge parentPresent
    have same := Option.some.inj (witnessPresent.symm.trans present)
    subst witnessNode
    exact Nat.le_trans before after

private theorem skip_write_cache (state : LocationState)
    (notDisabled : state.permission ≠ .Disabled) (skipped : skip state .Write .ForeignAccess = true) :
    state.idempotentForeignAccess = .Write := by
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

private theorem write_cache_retained (state : LocationState) (held : Bool)
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

/-- The minimal residual-independent condition needed for skipped Write
ancestors: each actual exposed Write contribution below them is nondroppable.
There is no legal-mask, classifier, operation-result or NoUB quantifier here. -/
def SkipStable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (support : UniIndex → Prop) : Prop :=
  ∀ query node,support query → tree.nodes.get query = some node →
    skip ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess = true →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      removable location protections maximum .Write witness witnessNode = false

/-- Local ownership, parent-cache ordering and existing scalar consistency
supply the extra call-time invariant. Disabled skips cannot have supporting
Write descendants; other skips force Write caches down to each contributor,
whose scalar bound then excludes the removable permission classes. -/
theorem skip_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentCacheOrder tree location)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (maximum : Option BorTag) : SkipStable tree location protections maximum rights.area.contains := by
  intro query node inside present skipped witness witnessNode found exposed walked supported
  have writable := rights.localRights query node inside present witness witnessNode found exposed walked .Write supported
  have notDisabled : ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled := writable.2.1
  have cache := skip_write_cache _ notDisabled skipped
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query witness witnessNode found _ walked
  have bound := path_cache_le tree location order query witness path node witnessNode present found
  rw [cache] at bound
  have witnessCache : ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess = .Write := by
    cases value : ((location.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess <;>
      simp_all [IdempotentForeignAccess.rank]
  have retained := write_cache_retained _ (protections.contains witnessNode.tag) (profile.present witness witnessNode found) witnessCache
  simp only [removable,retained,Bool.and_false]

/-- Every legal mask leaves the local contributor count of a Write-skipped
node unchanged under the independent SkipStable snapshot condition. -/
theorem residual_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (support : UniIndex → Prop)
    (stable : SkipStable tree location protections maximum support)
    (query : UniIndex) (node : TreeNode) (inside : support query) (present : tree.nodes.get query = some node)
    (skipped : skip ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess = true)
    (removed : List UniIndex) (legal : Removal tree location protections maximum .Write removed) :
    residualCount tree location protections .Write removed query =
      cardinality tree.nodes (effective location protections) query .Write := by
  unfold residualCount cardinality
  apply congrArg List.length
  apply List.filter_eq_self.mpr
  intro row member
  obtain ⟨entry,contributing⟩ := List.mem_filter.mp member
  have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp entry
  simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at contributing
  have nondroppable := stable query node inside present skipped row.1 row.2 found contributing.1.1 contributing.2 contributing.1.2
  have retained := nondroppable_retained tree location protections maximum .Write removed legal row.1 row.2 found nondroppable
  cases contained : removed.contains row.1 with
  | false => rfl
  | true => exact False.elim (retained (List.contains_iff_mem.mp contained))

end DuplicatePrefix.S05WriteCacheContributorOwnership
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05WriteCacheContributorOwnership.path_cache_le,
      ``DuplicatePrefix.S05WriteCacheContributorOwnership.skip_stable,
      ``DuplicatePrefix.S05WriteCacheContributorOwnership.residual_stable] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
