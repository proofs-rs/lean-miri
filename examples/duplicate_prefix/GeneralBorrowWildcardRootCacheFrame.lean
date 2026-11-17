import duplicate_prefix.GeneralBorrowWildcardVirtualLeaf
import duplicate_prefix.GeneralBorrowFreshLocation

namespace DuplicatePrefix.GeneralBorrowWildcardRootCacheFrame
open Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A genuine forest root has no ancestors. Its real cache update preserves
all other cache rows, for arbitrary initial counters and exposure levels. -/
theorem update_other (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (root query : UniIndex) (node : TreeNode)
    (present : nodes.get root = some node) (parentless : node.parent = none)
    (different : query ≠ root) (oldLevel newLevel : WildcardAccessLevel) :
    (cache.updateExposure nodes root oldLevel newLevel).cache.nodes.get query = cache.nodes.get query := by
  unfold ExposedCache.updateExposure
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    let changed := (scan () (cache,some root,0,.ok (),true))
    have first : ∃ nextCache, scan () (cache,some root,0,.ok (),true) =
        .yield (nextCache,none,1,.ok (),false) ∧ nextCache.nodes.get query = cache.nodes.get query := by
      simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,present,parentless]
      refine ⟨_,rfl,?_⟩
      exact GeneralBorrowFreshLocation.get_other cache.nodes root query _ different
    obtain ⟨nextCache,first,frame⟩ := first
    have last : scan () (nextCache,none,1,.ok (),false) =
        .done (nextCache,none,1,.ok (),false) := by simp [scan]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [first,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [last,bind,pure]
    exact frame
end DuplicatePrefix.GeneralBorrowWildcardRootCacheFrame
