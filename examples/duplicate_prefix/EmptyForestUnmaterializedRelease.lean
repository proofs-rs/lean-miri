import duplicate_prefix.GeneralBorrowFreshReleaseClean

namespace DuplicatePrefix.EmptyForestUnmaterializedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReleaseClean DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Releasing an unexposed zero-sized reservation with no materialized states
really scans all allocation locations, skips each absent permission, and returns
Released. Existing roots, ranges and exposure caches are preserved. -/
theorem release (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (unexposed : node.isExposed = false)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (protections : ProtectedTags) :
    tree.releaseProtector tag protections = ⟨tree,.Released⟩ := by
  have exposure : tree.updateExposureForProtectorRelease tag = ⟨tree,.ok ()⟩ := by
    unfold BorrowTree.updateExposureForProtectorRelease
    simp [tagged,present,unexposed,Id.run,pure]
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state = (none,tree) ∧ ∀ position ∈ remaining, position < tree.locations.entries.size
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases good with ⟨equal,bounded⟩
    subst state
    have valid := bounded position (by simp)
    refine ⟨(none,tree),?_,rfl,?_⟩
    · simp only [scan,index_exact tree.locations position valid,absent position valid]
    · intro query member
      exact bounded query (by simp [member])
  have finished := list_tail (List.range tree.locations.entries.size) scan property (none,tree)
    ⟨rfl,by intro position member;exact List.mem_range.mp member⟩ (List.nodup_range) step
  simp only [List.range_eq_range'] at finished
  rw [finished.1]
  simp only [exposure]

end DuplicatePrefix.EmptyForestUnmaterializedRelease
