import duplicate_prefix.EmptyForestUnmaterializedRelease

namespace DuplicatePrefix.S04ReturnReleaseInactive
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReleaseClean GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- Zero-window tags may acquire stored states from foreign accesses to the
same allocation. Release still skips them if they remain inactive, or if their
permission has no associated release access. Absence alone is not required. -/
def Quiescent (tree : BorrowTree) (index : UniIndex) : Prop :=
  ∀ position (valid : position < tree.locations.entries.size) state,
    tree.locations.entries[position].data.perms.get index = some state →
      state.accessed = false ∨ state.permission.associatedAccess = none

/-- The actual full allocation scan and exposure phase return the unchanged
tree. Arbitrary other nodes, stored permissions and exposed caches are retained. -/
theorem release (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (unexposed : node.isExposed = false) (quiet : Quiescent tree index)
    (protections : ProtectedTags) : tree.releaseProtector tag protections = ⟨tree,.Released⟩ := by
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
    intro position rest _ state good
    rcases good with ⟨equal,bounded⟩
    subst state
    have valid := bounded position (by simp)
    refine ⟨(none,tree),?_,rfl,?_⟩
    · cases stored : tree.locations.entries[position].data.perms.get index with
      | none => simp only [scan,index_exact tree.locations position valid,stored]
      | some value =>
        rcases quiet position valid value stored with inactive | noAccess
        · cases associated : value.permission.associatedAccess <;>
            simp only [scan,index_exact tree.locations position valid,stored,associated,inactive,
              Bool.false_eq_true,↓reduceIte]
        · simp only [scan,index_exact tree.locations position valid,stored,noAccess]
    · intro query member
      exact bounded query (by simp [member])
  have finished := list_tail (List.range tree.locations.entries.size) scan property (none,tree)
    ⟨rfl,by intro position member;exact List.mem_range.mp member⟩ (List.nodup_range) step
  simp only [List.range_eq_range'] at finished
  rw [finished.1]
  simp only [exposure]

/-- Earlier absence is a special case, not an extra condition on the final
zero-window state. -/
theorem of_absent (tree : BorrowTree) (index : UniIndex)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none) : Quiescent tree index := by
  intro position valid state stored
  rw [absent position valid] at stored
  contradiction

end DuplicatePrefix.S04ReturnReleaseInactive
