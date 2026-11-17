import duplicate_prefix.GeneralBorrowPartitionState
import duplicate_prefix.GeneralBorrowExposureRelease

namespace DuplicatePrefix.GeneralBorrowRootExposureFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Marking a real node exposed changes neither permission/topology view nor
allocator metadata. Exposure flags and caches are intentionally tracked separately. -/
theorem mark_shape (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) :
    treeShape {tree with nodes := tree.nodes.insert index {node with isExposed := true}} = treeShape tree := by
  have nodes := insert_existing_shape nodeShape tree.nodes index node {node with isExposed := true} present rfl
  simp only [treeShape,nodes]

/-- A cache-only update at an actual stored location preserves the exact
permission/topology view. No cache-correctness claim is inferred from this frame. -/
theorem cache_at (tree : BorrowTree) (position : Nat) (valid : position < tree.locations.entries.size)
    (cache : ExposedCache) :
    treeShape {tree with locations := (tree.locations.setAtPos position {tree.locations.entries[position].data with exposedCache := cache}).state} = treeShape tree := by
  rw [setAtPos_exact tree.locations position valid]
  have maps : (replaced tree.locations position valid {tree.locations.entries[position].data with exposedCache := cache}).entries.map
      (fun segment => (segment.range,locationShape segment.data)) =
      tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) := by
    apply Array.ext
    · simp [replaced]
    · intro query left right
      simp only [replaced,Array.getElem_map,Array.getElem_set]
      by_cases same : position = query
      · subst query;simp only [ite_true];rfl
      · simp only [same,ite_false]
  simp only [treeShape,maps]

/-- The actual exposeTag operation completes on a present node of a bounded
acyclic graph, and preserves permissions, graph and allocator metadata. Actual
counter updates are performed; no success, empty cache or cache witness is a premise. -/
theorem expose (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (depth : ParentDepth tree.nodes) (unexposed : node.isExposed = false) (protections : ProtectedTags) :
    (tree.exposeTag protections tag).outcome = .ok () ∧
    treeShape (tree.exposeTag protections tag).tree = treeShape tree ∧
    (tree.exposeTag protections tag).tree.nodes = tree.nodes.insert index {node with isExposed := true} := by
  let marked := {tree with nodes := tree.nodes.insert index {node with isExposed := true}}
  have markedShape := mark_shape tree index node present
  have markedPresent : marked.nodes.get index = some {node with isExposed := true} := GeneralBorrowFreshLocation.get_same tree.nodes index _
  let markedDepth := GeneralBorrowFreshMetadata.parent_depth tree marked markedShape depth
  unfold BorrowTree.exposeTag
  simp only [tagged,present,unexposed,Bool.false_eq_true,↓reduceIte,Id.run,pure]
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  name_release_exposure_scan
  let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    state.1 = none ∧ treeShape state.2 = treeShape marked ∧ state.2.nodes = marked.nodes ∧
      state.2.locations.entries.size = marked.locations.entries.size
  have step : ∀ position member state, property state → property (scan position member state).value := by
    intro position member state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,shape,nodes,size⟩
    dsimp only at returnedEq shape nodes size
    subst returned
    have originalBound : position < marked.locations.entries.size := by
      have bound := List.mem_range'_1.mp member
      simpa [marked] using bound.2
    have valid : position < current.locations.entries.size := by rw [size];exact originalBound
    let location := current.locations.entries[position].data
    let state := (location.perms.get index).getD node.defaultLocationState
    let level := state.permission.strongestAllowedLocalAccess (protections.contains tag)
    let update := location.exposedCache.updateExposure marked.nodes index .None level
    let nextLocation := {location with exposedCache := update.cache}
    let nextTree := {current with locations := (current.locations.setAtPos position nextLocation).state}
    have cacheOK : update.outcome = .ok () := update_exposure_succeeds location.exposedCache marked.nodes markedDepth index _ markedPresent .None level
    have actual : scan position member (none,current) = .yield (none,nextTree) := by
      simp only [scan,index_exact current.locations position valid]
      dsimp only [location,state,level,update,marked] at cacheOK
      simp only [cacheOK,Except.mapError,setAtPos_success current.locations position valid]
      rfl
    rw [actual]
    refine ⟨rfl,(cache_at current position valid update.cache).trans shape,nodes,
      (setAtPos_length current.locations position valid nextLocation).trans size⟩
  have initial : property (none,marked) := ⟨rfl,rfl,rfl,rfl⟩
  have final := GeneralBorrowLoop.list_invariant' _ scan property step _ initial
  rw [final.1]
  exact ⟨rfl,final.2.1.trans markedShape,final.2.2.1⟩

/-- Re-exposing the same already exposed node is the real source early return;
no counter is incremented again. -/
theorem already (tree : BorrowTree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (exposed : node.isExposed = true) (protections : ProtectedTags) :
    tree.exposeTag protections tag = ⟨tree,.ok ()⟩ := by
  simp only [BorrowTree.exposeTag,tagged,present,exposed,↓reduceIte,Id.run,pure]

end DuplicatePrefix.GeneralBorrowRootExposureFrame
