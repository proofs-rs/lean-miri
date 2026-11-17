import duplicate_prefix.GeneralBorrowWildcardSubtreeRegion
import duplicate_prefix.GeneralBorrowWildcardSubtreeComplete
import duplicate_prefix.GeneralBorrowWildcardForestWeights
import duplicate_prefix.GeneralBorrowVirtualRootsAdapter

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeRegionFold
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem run_from (tree : BorrowTree) (initial : LocationTree) (kind : AccessKind) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (region : Region tree initial kind protections) (roots : List UniIndex) (maximum : Option BorTag)
    (supported : ∀ root ∈ roots, region.support root)
    (current : LocationTree) (owned : Owned region current) (cache : current.exposedCache = initial.exposedCache) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots current maximum kind protections = ⟨after,.Completed⟩ ∧
      Owned region after ∧ after.exposedCache = initial.exposedCache ∧
      (∀ query, ¬region.support query → after.perms.get query = current.perms.get query) := by
  induction roots generalizing current with
  | nil => exact ⟨current,rfl,owned,cache,by intro query outside;rfl⟩
  | cons root rest ih =>
    let facts := data region current owned cache root (supported root (by simp))
    let weights := GeneralBorrowWildcardForestWeights.of_forest tree current protections forest
    have first := GeneralBorrowWildcardSubtreeComplete.access tree current root maximum kind protections weights
      (GeneralBorrowWildcardForestWeights.bounded tree current protections forest root) facts
    let called := tree.performWildcardAccessAt current root maximum kind protections true
    have nextOwned : Owned region called.location := first.2.1
    have nextCache : called.location.exposedCache = initial.exposedCache := first.2.2.1.trans cache
    obtain ⟨after,tail,afterOwned,afterCache,afterFrame⟩ := ih (fun root member => supported root (by simp [member])) called.location nextOwned nextCache
    refine ⟨after,?_,afterOwned,afterCache,?_⟩
    · have status : (tree.performWildcardAccessAt current root maximum kind protections true).status = .Completed := first.1
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,status,beq_self_eq_true,ite_true] using tail
    · intro query outside
      exact (afterFrame query outside).trans (first.2.2.2 query outside)

/-- Any finite actual source-order extra-subtree schedule completes while
retaining the entire common support, unchanged counters and the outside frame.
Repeated/overlapping supported roots are allowed; no per-call success is assumed. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (kind : AccessKind) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (region : Region tree initial kind protections) (roots : List UniIndex) (maximum : Option BorTag)
    (supported : ∀ root ∈ roots, region.support root) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots initial maximum kind protections = ⟨after,.Completed⟩ ∧
      Owned region after ∧ after.exposedCache = initial.exposedCache ∧
      (∀ query, ¬region.support query → after.perms.get query = initial.perms.get query) :=
  run_from tree initial kind protections forest region roots maximum supported initial region.owned rfl

/-- Data-derived completion joins the finite calls to the actual indexed
nonzero root-position callback, preserving source order and its concrete-root
skip rule. Every wildcard visitor uses the original virtual-root flag. -/
theorem indexed (tree : BorrowTree) (initial : LocationTree) (kind : AccessKind) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (region : Region tree initial kind protections) (primary : UniIndex) (roots : List UniIndex) (maximum : BorTag)
    (range : ByteRange) (supported : ∀ root ∈ roots, region.support root)
    (different : ∀ root ∈ roots, root ≠ primary) :
    ∃ after,
      forIn (List.range' 1 roots.length) (initial,none,false)
        (GeneralBorrowVirtualRootsAdapter.scanAt tree primary roots maximum kind protections range) = (after,none,false) ∧
      Owned region after ∧ after.exposedCache = initial.exposedCache ∧
      (∀ query, ¬region.support query → after.perms.get query = initial.perms.get query) := by
  obtain ⟨after,completed,owned,cache,frame⟩ := access tree initial kind protections forest region roots (some maximum) supported
  refine ⟨after,?_,owned,cache,frame⟩
  rw [GeneralBorrowVirtualRootsAdapter.indexed]
  exact GeneralBorrowVirtualRootsAdapter.successful tree primary maximum kind protections range roots different initial after completed

end DuplicatePrefix.GeneralBorrowWildcardSubtreeRegionFold
