import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.GeneralBorrowStarExposureCounts
namespace DuplicatePrefix.GeneralBorrowUniqueRootExposure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.RangeMapNonempty
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposureHistoryBounds DuplicatePrefix.GeneralBorrowStarExposureCounts
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def bump (cache : ExposedCache) (root : UniIndex) : ExposedCache :=
  let old := (cache.nodes.get root).getD {}
  {cache with nodes := cache.nodes.insert root {localReads := old.localReads+1,localWrites := old.localWrites+1}}

theorem root_cache (cache : ExposedCache) (nodes : UniValMap TreeNode) (root : UniIndex) (node : TreeNode)
    (present : nodes.get root = some node) (parentless : node.parent = none) :
    cache.updateExposure nodes root .None .Write = ⟨bump cache root,.ok ()⟩ := by
  unfold ExposedCache.updateExposure
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have first : scan () (cache,some root,0,.ok (),true) = .yield (bump cache root,none,1,.ok (),false) := by
    simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,present,parentless,Option.isNone_none]
    rfl
  have last : scan () (bump cache root,none,1,.ok (),false) = .done (bump cache root,none,1,.ok (),false) := by
    simp only [scan,Bool.false_eq_true,↓reduceIte]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [first,bind]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [last,bind,pure]
  rfl

/-- Real root exposure updates both counters at the parentless Unique root. -/
theorem expose (tree : BorrowTree) (tag : BorTag) (root : UniIndex) (node : TreeNode)
    (location : LocationTree) (capacity : UInt64) (protections : ProtectedTags)
    (tagged : tree.indexOfTag tag = some root) (present : tree.nodeAt root = some node)
    (parentless : node.parent = none) (unexposed : node.isExposed = false)
    (unique : ∃ state, location.perms.get root = some state ∧ state.permission = .Unique)
    (locations : tree.locations = homogeneous capacity location) :
    tree.exposeTag protections tag =
      ⟨{(marked tree root node) with locations := homogeneous capacity {location with exposedCache := bump location.exposedCache root}},.ok ()⟩ := by
  obtain ⟨state,stored,permission⟩ := unique
  have now : (marked tree root node).nodes.get root = some {node with isExposed := true} :=
    GeneralBorrowFreshLocation.get_same tree.nodes root _
  have update := root_cache location.exposedCache (marked tree root node).nodes root {node with isExposed := true} now parentless
  unfold BorrowTree.exposeTag
  simp only [tagged,present,unexposed,Bool.false_eq_true,↓reduceIte]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,locations,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  simp only [show (homogeneous capacity location).entries.size = 1 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn'_cons,List.forIn'_nil,bind,pure]
  simp only [index_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  simp only [homogeneous,Array.getElem_singleton] at *
  simp only [stored,Option.getD_some,permission,Permission.strongestAllowedLocalAccess]
  erw [update]
  simp only [Except.mapError]
  erw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  with_unfolding_all rfl

/-- After the root is exposed, Nat counters record N+1 reads and one write;
all leaf counters retain their exact earlier cardinality. -/
theorem counts (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex)
    (good : Counts cache root leaves) (room : leaves.length+1 < 65536) :
    reads (bump cache root) root = leaves.length+1 ∧ writes (bump cache root) root = 1 ∧
    (∀ query, query ≠ root → reads (bump cache root) query = leaves.count query ∧ writes (bump cache root) query = 0) := by
  have rootRead := good.rootReads
  have rootWrite := good.allWrites root
  refine ⟨?_,?_,?_⟩
  · simp only [reads,bump,GeneralBorrowFreshLocation.get_same,Option.getD_some,UInt16.toNat_add]
    change (reads cache root+1)%65536 = leaves.length+1
    rw [rootRead,Nat.mod_eq_of_lt room]
  · simp only [writes,bump,GeneralBorrowFreshLocation.get_same,Option.getD_some,UInt16.toNat_add]
    change (writes cache root+1)%65536 = 1
    rw [rootWrite]
  · intro query different
    simp only [reads,writes,bump,GeneralBorrowFreshLocation.get_other _ _ _ _ different]
    exact ⟨good.otherReads query different,good.allWrites query⟩
end DuplicatePrefix.GeneralBorrowUniqueRootExposure
