import duplicate_prefix.S05PotentialContributorExposure
import duplicate_prefix.GeneralBorrowAllocationSifaConsistency
import duplicate_prefix.GeneralBorrowProtectorCacheMap

namespace DuplicatePrefix.S05LiveSubtreeCacheSoundness
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowSifaPermissionConsistency GeneralRangeMapState
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization S05WriteCacheContributorOwnership
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert

/-- A live Write cone has no Disabled/Frozen barrier on its finite physical
ancestor segment. Exposure/protector bits do not define barriers: protector
removal can create Write support without changing this cone. Inaccessible
subtrees behind a barrier impose no descendant idempotence requirement. -/
def LiveCone (tree : BorrowTree) (location : LocationTree) (query witness : UniIndex) : Prop :=
  ∀ middle node,tree.nodes.get middle = some node →
    query ∈ walk tree.nodes (tree.nodes.size+1) middle →
    middle ∈ walk tree.nodes (tree.nodes.size+1) witness →
    let state := (location.perms.get middle).getD node.defaultLocationState
    state.permission ≠ .Disabled ∧ state.permission ≠ .Frozen

/-- Raw cached-ancestor strength is bounded by a live descendant's numeric
permission-table idempotence, NOT by its cached value. Consistent here is the
existing strongestIdempotentForeignAccess table bound on a synthetic cache
field; it contains no operation result, future witness, or NoUB.
This candidate is not a definition of ordinary call-time wellformedness. -/
def Soundness (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) : Prop :=
  ∀ query node,support query → tree.nodes.get query = some node →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → LiveCone tree location query witness →
      Consistent { (location.perms.get witness).getD witnessNode.defaultLocationState with
        idempotentForeignAccess := ((location.perms.get query).getD node.defaultLocationState).idempotentForeignAccess }
        (protections.contains witnessNode.tag)

private theorem area_path {tree : BorrowTree} {root query target : UniIndex}
    (area : GeneralBorrowWildcardControlStack.Support tree root) (graph : Reciprocal tree)
    (inside : area.contains query) (path : Path tree query target) : area.contains target := by
  induction path with
  | refl node present => exact inside
  | @step parent child earlier node present edge ih =>
    obtain ⟨parentNode,parentPresent,member⟩ := graph child node present parent edge
    exact area.children parent parentNode ih parentPresent child member

/-- Existing local ownership makes each relevant exposed Write support path
live; no Disabled/Frozen shortcut is assumed to constrain inaccessible nodes. -/
theorem live_of_ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (query witness : UniIndex) (witnessNode : TreeNode) (inside : rights.area.contains query)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    LiveCone tree location query witness := by
  intro middle node present queryWalk witnessWalk
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query middle node present _ queryWalk
  have middleInside := area_path rights.area graph inside path
  have writable := rights.localRights middle node middleInside present witness witnessNode found exposed witnessWalk .Write supported
  exact ⟨writable.2.1,writable.2.2.1⟩

private theorem skipped_cache (state : LocationState) (notDisabled : state.permission ≠ .Disabled)
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

private theorem write_bound_retained (state : LocationState) (held : Bool)
    (bound : Consistent {state with idempotentForeignAccess := .Write} held) :
    losesWriteWhenForeign state.permission = false := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;>
      simp_all [Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank,losesWriteWhenForeign]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> simp_all [Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank,losesWriteWhenForeign]

/-- Numeric live-cone cache soundness supplies the required SkipStable without
ordering descendant cached values. Raw local ownership justifies the live cone. -/
theorem skip_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (sound : Soundness tree location protections rights.area.contains) (maximum : Option BorTag) :
    SkipStable tree location protections maximum rights.area.contains := by
  intro query node inside present skipped witness witnessNode found exposed walked supported
  have writable := rights.localRights query node inside present witness witnessNode found exposed walked .Write supported
  have cache := skipped_cache _ writable.2.1 skipped
  have live := live_of_ownership tree location protections root position rights depth graph query witness witnessNode inside found exposed supported
  have bound := sound query node inside present witness witnessNode found walked live
  rw [cache] at bound
  have retained := write_bound_retained _ (protections.contains witnessNode.tag) bound
  simp only [removable,retained,Bool.and_false]

/-- Removing protection cannot lower a permission's numeric idempotence bound.
Live cones are unchanged because barriers depend only on physical permission. -/
theorem remove_protector (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (support : UniIndex → Prop) (tag : BorTag) (sound : Soundness tree location protections support) :
    Soundness tree location (protections.remove tag) support := by
  intro query node inside present witness witnessNode found walked live
  have bound := sound query node inside present witness witnessNode found walked live
  by_cases same : witnessNode.tag = tag
  · rw [same] at bound ⊢
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    cases held : protections.contains tag with
    | false => simpa only [held] using bound
    | true => exact GeneralBorrowSifaPermissionConsistency.unprotect _ (by simpa only [held] using bound)
  · simpa only [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.remove_other protections tag witnessNode.tag same] using bound

/-- Real allocation initializes the table relation, including lazy defaults.
Its unique node makes every applicable pair reflexive; the actual scalar
initialization theorem supplies the permission-table bound. -/
theorem allocation (capacity : UInt64) (tag : BorTag) (protections : ProtectedTags) (support : UniIndex → Prop) :
    Every (fun location => Soundness (BorrowTree.new tag (Size.ofBytes capacity)) location protections support)
      (BorrowTree.new tag (Size.ofBytes capacity)).locations := by
  have profile := GeneralBorrowAllocationSifaConsistency.allocation capacity tag protections
  intro position valid query node _ present witness witnessNode found _ _
  have queryBound := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes query node present
  have witnessBound := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes witness witnessNode found
  have size : (BorrowTree.new tag (Size.ofBytes capacity)).nodes.data.size = 1 := by
    simp [BorrowTree.new,UniValMap.insert,UniValMap.extendTo,Id.run,bind,pure]
    rfl
  rw [size] at queryBound witnessBound
  have same := GeneralBorrowNodeUpdate.index_injective query witness (by omega)
  subst witness
  have sameNode := Option.some.inj (present.symm.trans found)
  subst witnessNode
  exact (profile position valid).present query node present

end DuplicatePrefix.S05LiveSubtreeCacheSoundness
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05LiveSubtreeCacheSoundness.live_of_ownership,
      ``DuplicatePrefix.S05LiveSubtreeCacheSoundness.skip_stable,
      ``DuplicatePrefix.S05LiveSubtreeCacheSoundness.remove_protector,
      ``DuplicatePrefix.S05LiveSubtreeCacheSoundness.allocation] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
