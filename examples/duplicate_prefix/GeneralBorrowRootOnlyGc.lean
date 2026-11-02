import duplicate_prefix.GeneralBorrowRootOnlyActivatedHistory
import duplicate_prefix.GeneralBorrowPartitionGc
namespace DuplicatePrefix.GeneralBorrowRootOnlyGc
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyMixedHistory DuplicatePrefix.GeneralBorrowRootOnlyExposureExact
open DuplicatePrefix.GeneralBorrowRootOnlyRangeCache DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold DuplicatePrefix.GeneralBorrowGcRangeClean
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
abbrev root : UniIndex := GeneralBorrowFullSharedSeed.root

/-- The protocol's original allocation root is physical slot zero. Its exact
cache has no child entries, so deleting any distinct child is cache-neutral. -/
theorem remove_cache (index : UniIndex) (different : index ≠ root) (flag : Bool) :
    (cacheFor root flag).remove index = cacheFor root flag := by
  have nonzero : index.toNat ≠ 0 := fun same => different (GeneralBorrowNodeUpdate.index_injective index root same)
  cases flag with
  | false => rfl
  | true =>
    have exactCache : cacheFor root true = GeneralBorrowRootExposureSeed.exposedLocation.exposedCache := rfl
    rw [exactCache]
    unfold ExposedCache.remove UniValMap.remove
    change ({nodes := (if h : index.toNat < 1 then _ else _)} : ExposedCache) = _
    rw [dite_eq_right (by omega)]

private theorem trim_fixed {α : Type} (map : UniValMap α) (last : map.data.back? ≠ some none) :
    map.trimTrailingNone = map := by
  unfold UniValMap.trimTrailingNone
  simp only [Id.run,bind,pure,ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  cases back : map.data.back? with
  | none => simp only [Bool.false_eq_true,↓reduceIte,bind,pure]
  | some value =>
    cases value with
    | none => exact False.elim (last back)
    | some value => simp only [Bool.false_eq_true,↓reduceIte,bind,pure]

/-- Canonical empty/root-singleton cache maps already have no trailing None. -/
theorem trim_cache (flag : Bool) : (cacheFor root flag).nodes.trimTrailingNone = (cacheFor root flag).nodes := by
  cases flag with
  | false => exact trim_fixed _ (by decide)
  | true =>
    have exactCache : cacheFor root true = GeneralBorrowRootExposureSeed.exposedLocation.exposedCache := rfl
    rw [exactCache]
    exact trim_fixed _ (by decide)

/-- Arbitrary source node deletion preserves the conditional root invariant.
If the root is deleted its root-present clause is vacuous; real star GC never
deletes that root, as proved separately by its structural completion theorem. -/
theorem remove (tree : BorrowTree) (index : UniIndex) (good : Invariant tree root) :
    Invariant (source_remove_useless_node tree index).1 root := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using good
  | some removed =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    refine ⟨?_,?_⟩
    · intro query node present exposed
      have different : query ≠ index := by
        intro same;subst query
        rw [GeneralBorrowFreshDeassignment.get_removed] at present
        cases present
      rw [GeneralBorrowSparseRemoval.remove_get_other _ index query different] at present
      exact good.1 query node present exposed
    · intro node present
      have different : root ≠ index := by
        intro same;subst index
        rw [GeneralBorrowFreshDeassignment.get_removed] at present
        cases present
      rw [GeneralBorrowSparseRemoval.remove_get_other _ index root different] at present
      intro position valid
      have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
      obtain ⟨⟨state,found,unique⟩,cache⟩ := good.2 node present position previous
      simp only [DedupRangeMap.modifyAll,Array.getElem_map]
      refine ⟨⟨state,?_,unique⟩,?_⟩
      · exact (GeneralBorrowSparseRemoval.remove_get_other _ index root different).trans found
      · rw [cache]
        exact remove_cache index (Ne.symm different) node.isExposed

/-- Rebuilding the original root's children retains its flag and all locations. -/
theorem update_root (tree : BorrowTree) (node : TreeNode) (children : Array UniIndex)
    (present : tree.nodes.get root = some node) (good : Invariant tree root) :
    Invariant {tree with nodes := tree.nodes.insert root {node with children := children}} root := by
  refine ⟨GeneralBorrowRootOnlySharedFrames.insert_root tree root _ good.1,?_⟩
  intro next found
  rw [GeneralBorrowFreshLocation.get_same] at found
  cases found
  exact good.2 node present

/-- Actual trailing-None normalization retains the exact canonical protocol
cache and each root Unique permission; lookup preservation handles permissions. -/
theorem trim (tree : BorrowTree) (good : Invariant tree root) :
    Invariant {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} root := by
  refine ⟨good.1,?_⟩
  intro node present position valid
  have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  obtain ⟨⟨state,found,unique⟩,cache⟩ := good.2 node present position previous
  simp only [DedupRangeMap.modifyAll,Array.getElem_map]
  refine ⟨⟨state,(trim_location_get _ root).trans found,unique⟩,?_⟩
  change ({nodes := tree.locations.entries[position].data.exposedCache.nodes.trimTrailingNone} : ExposedCache) = _
  rw [cache,trim_cache]

theorem merge (tree : BorrowTree) (good : Invariant tree root) :
    Invariant {tree with locations := tree.locations.mergeAdjacentThorough.state} root := by
  exact ⟨good.1,fun node present => GeneralRangeMapThoroughEvery.preserves _ tree.locations (good.2 node present)⟩

/-- The actual star walker removes only leaves and rewrites only root children;
the exact conditional cache invariant survives the entire postorder walk. -/
theorem children (tree : BorrowTree) (node : TreeNode) (live : Array BorTag)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node) (good : Invariant tree root) :
    Invariant (source_gc_children tree root live).tree root := by
  have notChild : root ∉ node.children.toList := fun member => ((star.children root).mp member).1 rfl
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (star.children index).mp member
    exact ⟨child,present,(star.leaves index child present different).2⟩
  obtain ⟨after,kept,walked,rootPresent,capacity,folded⟩ := GeneralBorrowGcStarWalk.complete tree root node live
    star.present star.distinct notChild leaves (GeneralBorrowGeneratedStarShape.children_bound tree root node star)
  obtain ⟨other,result,done,_,_,policy⟩ := GeneralBorrowGcLeafProperty.complete (fun tree => Invariant tree root)
    (fun current index initial => remove current index initial)
    node.children.toList tree tree root root live #[] star.distinct leaves good
  have same := congrArg (fun row : Option BorrowTree.TreeGcResult × BorrowTree × Array UniIndex => row.2.1) (folded.symm.trans done)
  change after = other at same
  subst other
  rw [walked]
  exact update_root after node kept rootPresent policy

/-- Full real collection and its physical normalization/merge preserve cache
coherence for the selected root-only allocation protocol. This theorem does not
claim cache coherence for arbitrary exposed children or arbitrary forests. -/
theorem preserves (tree : BorrowTree) (node : TreeNode) (live : Array BorTag)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node) (roots : tree.roots = #[root])
    (good : Invariant tree root) : Invariant (tree.removeUnreachableTags live).tree root := by
  have walked := children tree node live star good
  have notChild : root ∉ node.children.toList := fun member => ((star.children root).mp member).1 rfl
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (star.children index).mp member
    exact ⟨child,present,(star.leaves index child present different).2⟩
  obtain ⟨after,kept,exactWalk,_,_,_⟩ := GeneralBorrowGcStarWalk.complete tree root node live
    star.present star.distinct notChild leaves (GeneralBorrowGeneratedStarShape.children_bound tree root node star)
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [exactWalk]
  have finished := merge _ (trim _ walked)
  unfold BorrowTree.removeUnreachableTags
  rw [roots]
  simp only [Id.run,bind,pure,←Array.forIn_toList,
    List.forIn_cons,List.forIn_nil]
  rw [show (gc_root_children tree root live).outcome = .ok () from success]
  simp only []
  split <;> exact finished

end DuplicatePrefix.GeneralBorrowRootOnlyGc
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyGc." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only GC dependency {dependency}"
