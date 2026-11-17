import duplicate_prefix.GeneralBorrowExposureRelease
import duplicate_prefix.GeneralBorrowFreshInstallation
namespace DuplicatePrefix.GeneralBorrowExposeRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureRelease
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def bumpRead (cache : ExposedCache) (index : UniIndex) : ExposedCache :=
  let old := (cache.nodes.get index).getD {}
  {cache with nodes := cache.nodes.insert index {old with localReads := old.localReads+1}}

/-- Exact source update along a leaf and its parentless root. UInt16 arithmetic
is retained, including wrap. Permission states are outside this cache operation. -/
theorem two_nodes (cache : ExposedCache) (nodes : UniValMap TreeNode) (leaf root : UniIndex)
    (leafNode rootNode : TreeNode) (leafPresent : nodes.get leaf = some leafNode)
    (rootPresent : nodes.get root = some rootNode) (parent : leafNode.parent = some root)
    (parentless : rootNode.parent = none) :
    cache.updateExposure nodes leaf .None .Read =
      ⟨bumpRead (bumpRead cache leaf) root,.ok ()⟩ := by
  have nonempty : 0 < nodes.size := by
    have valid := lookup_valid nodes root rootNode rootPresent
    unfold UniValMap.size
    omega
  have notPast : ¬ 1 > nodes.size := by omega
  unfold ExposedCache.updateExposure
  simp only [reduceCtorEq,↓reduceIte,Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have first : scan () (cache,some leaf,0,.ok (),true) =
      .yield (bumpRead cache leaf,some root,1,.ok (),true) := by
    simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,leafPresent,parent,Option.isNone_some]
    rfl
  have second : scan () (bumpRead cache leaf,some root,1,.ok (),true) =
      .yield (bumpRead (bumpRead cache leaf) root,none,2,.ok (),false) := by
    simp only [scan,notPast,↓reduceIte,rootPresent,parentless,Option.isNone_none]
    rfl
  have last : scan () (bumpRead (bumpRead cache leaf) root,none,2,.ok (),false) =
      .done (bumpRead (bumpRead cache leaf) root,none,2,.ok (),false) := by simp [scan,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [first,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [second,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [last,bind,pure]
  rfl

def marked (tree : BorrowTree) (leaf : UniIndex) (node : TreeNode) : BorrowTree :=
  {tree with nodes := tree.nodes.insert leaf {node with isExposed := true}}

/-- Exposing a previously unexposed Frozen reference executes both real ancestor
counter updates, returns success, and preserves every permission-map entry. -/
theorem expose (tree : BorrowTree) (tag : BorTag) (leaf root : UniIndex) (leafNode rootNode : TreeNode)
    (location : LocationTree) (capacity : UInt64) (protections : ProtectedTags)
    (tagged : tree.indexOfTag tag = some leaf) (leafPresent : tree.nodeAt leaf = some leafNode)
    (rootPresent : tree.nodeAt root = some rootNode) (different : root ≠ leaf)
    (parent : leafNode.parent = some root) (parentless : rootNode.parent = none)
    (unexposed : leafNode.isExposed = false)
    (frozen : ∃ state, location.perms.get leaf = some state ∧ state.permission = .Frozen)
    (locations : tree.locations = homogeneous capacity location) :
    tree.exposeTag protections tag =
      ⟨{(marked tree leaf leafNode) with locations := homogeneous capacity ({location with exposedCache := bumpRead (bumpRead location.exposedCache leaf) root})},.ok ()⟩ := by
  obtain ⟨state,stored,permission⟩ := frozen
  have leafNow : (marked tree leaf leafNode).nodes.get leaf = some {leafNode with isExposed := true} :=
    GeneralBorrowFreshLocation.get_same tree.nodes leaf _
  have rootNow : (marked tree leaf leafNode).nodes.get root = some rootNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes leaf root _ different).trans rootPresent
  have update := two_nodes location.exposedCache (marked tree leaf leafNode).nodes leaf root
    {leafNode with isExposed := true} rootNode leafNow rootNow parent parentless
  unfold BorrowTree.exposeTag
  simp only [tagged,leafPresent,unexposed,Bool.false_eq_true,↓reduceIte]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,locations,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  simp only [show (homogeneous capacity location).entries.size = 1 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn'_cons,List.forIn'_nil]
  simp only [bind,pure]
  simp only [index_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  simp only [homogeneous] at *
  dsimp only [marked] at update
  simp only [Array.getElem_singleton,stored,Option.getD_some,permission,
    Permission.strongestAllowedLocalAccess,update,Except.mapError,Except.map,bind,pure]
  rw [setAtPos_exact (⟨#[⟨⟨0,capacity⟩,location⟩]⟩ : DedupRangeMap LocationTree) 0 (by change 0<1;decide)]
  with_unfolding_all rfl
end DuplicatePrefix.GeneralBorrowExposeRead
