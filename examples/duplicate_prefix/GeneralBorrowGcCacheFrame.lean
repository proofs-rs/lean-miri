import duplicate_prefix.GeneralBorrowGcCacheContractionCoherent
import duplicate_prefix.GeneralBorrowGcNodeFieldsWhile
import duplicate_prefix.GeneralBorrowGcRootInvariant

namespace DuplicatePrefix.GeneralBorrowGcCacheFrame
open Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowExposureAncestorFold DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual GC never changes a surviving query's permission slot or counters.
Absent query counters are zero. This remains valid at temporarily dangling
primitive boundaries and does NOT assert cache cardinality there. -/
structure Frame (before : LocationTree) (nodes : UniValMap TreeNode) (after : LocationTree) : Prop where
  stored : ∀ query node,nodes.get query = some node → after.perms.get query = before.perms.get query
  counters : ∀ query node,nodes.get query = some node → ∀ kind,counter after.exposedCache query kind = counter before.exposedCache query kind
  vacant : ∀ query,nodes.get query = none → ∀ kind,counter after.exposedCache query kind = 0

def Witness (original : BorrowTree) (protections : ProtectedTags) (current : BorrowTree) (location : LocationTree) : Prop :=
  ∃ before,LocationCoherent original before protections ∧ Frame before current.nodes location

def Property (original : BorrowTree) (protections : ProtectedTags) (current : BorrowTree) : Prop :=
  Every (Witness original protections current) current.locations

private theorem absent_zero (tree : BorrowTree) (depth : ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (good : LocationCoherent tree location protections)
    (query : UniIndex) (missing : tree.nodes.get query = none) (kind : AccessKind) :
    counter location.exposedCache query kind = 0 := by
  rw [good query kind]
  have absent : GeneralBorrowExposureGraphTransport.sources tree.nodes (effective location protections) query kind = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index member
    obtain ⟨node,present,_,_,walked⟩ := (GeneralBorrowExposureGraphTransport.member _ _ _ _ _).mp member
    obtain ⟨⟨value,found⟩,_⟩ := GeneralBorrowExposureAncestorDistinct.present_depth tree.nodes depth
      (tree.nodes.size+1) index node present query walked
    rw [missing] at found
    cases found
  have size := congrArg List.length absent
  have zero : cardinality tree.nodes (effective location protections) query kind = 0 := by
    simpa only [GeneralBorrowExposureGraphTransport.sources,List.length_map,List.length_nil,cardinality] using size
  rw [zero]
  rfl

theorem initial (tree : BorrowTree) (protections : ProtectedTags) (depth : ParentDepth tree.nodes)
    (good : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    Property tree protections tree := by
  intro position valid
  let location := tree.locations.entries[position].data
  refine ⟨location,good position valid,?_,?_,?_⟩
  · intro query node present;rfl
  · intro query node present kind;rfl
  · intro query missing kind
    exact absent_zero tree depth location protections (good position valid) query missing kind

private theorem removed (original tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex)
    (good : Property original protections tree) : Property original protections (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using good
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    intro position valid
    have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
    obtain ⟨before,initial,frame⟩ := good position previous
    refine ⟨before,initial,?_,?_,?_⟩
    · intro query value found
      have different : query ≠ index := by intro same;subst query;rw [GeneralBorrowFreshDeassignment.get_removed] at found;cases found
      rw [GeneralBorrowSparseRemoval.remove_get_other _ index query different] at found
      simpa only [DedupRangeMap.modifyAll,Array.getElem_map,GeneralBorrowSparseRemoval.remove_get_other _ index query different] using frame.stored query value found
    · intro query value found kind
      have different : query ≠ index := by intro same;subst query;rw [GeneralBorrowFreshDeassignment.get_removed] at found;cases found
      rw [GeneralBorrowSparseRemoval.remove_get_other _ index query different] at found
      have cacheFrame : ∀ location : LocationTree,counter (location.exposedCache.remove index) query kind = counter location.exposedCache query kind := by
        intro location
        cases kind <;> simp only [counter,ExposedCache.remove,GeneralBorrowSparseRemoval.remove_get_other _ index query different]
      simpa only [DedupRangeMap.modifyAll,Array.getElem_map,cacheFrame] using frame.counters query value found kind
    · intro query missing kind
      by_cases same : query = index
      · subst query
        cases kind <;> simp only [counter,DedupRangeMap.modifyAll,Array.getElem_map,ExposedCache.remove,GeneralBorrowFreshDeassignment.get_removed,Option.getD_none]
        all_goals rfl
      · rw [GeneralBorrowSparseRemoval.remove_get_other _ index query same] at missing
        have cacheFrame : ∀ location : LocationTree,counter (location.exposedCache.remove index) query kind = counter location.exposedCache query kind := by
          intro location
          cases kind <;> simp only [counter,ExposedCache.remove,GeneralBorrowSparseRemoval.remove_get_other _ index query same]
        simpa only [DedupRangeMap.modifyAll,Array.getElem_map,cacheFrame] using frame.vacant query missing kind

private theorem updated (original tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex)
    (old new : TreeNode) (present : tree.nodes.get index = some old)
    (good : Property original protections tree) :
    Property original protections {tree with nodes := tree.nodes.insert index new} := by
  intro position valid
  obtain ⟨before,initial,frame⟩ := good position valid
  have back : ∀ query value,(tree.nodes.insert index new).get query = some value → ∃ previous,tree.nodes.get query = some previous := by
    intro query value found
    by_cases same : query = index
    · subst query;exact ⟨old,present⟩
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ index query old new present same] at found
      exact ⟨value,found⟩
  refine ⟨before,initial,?_,?_,?_⟩
  · intro query value found
    obtain ⟨previous,oldFound⟩ := back query value found
    exact frame.stored query previous oldFound
  · intro query value found kind
    obtain ⟨previous,oldFound⟩ := back query value found
    exact frame.counters query previous oldFound kind
  · intro query missing kind
    have different : query ≠ index := by
      intro same;subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same _ index old new present] at missing
      cases missing
    rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ index query old new present different] at missing
    exact frame.vacant query missing kind

/-- Arbitrary actual source component GC preserves exact surviving-query
lookup witnesses, including early error states. No forest/success input. -/
theorem children (original tree : BorrowTree) (protections : ProtectedTags) (root : UniIndex)
    (live : Array BorTag) (good : Property original protections tree) :
    Property original protections (source_gc_children tree root live).tree := by
  exact GeneralBorrowGcNodeFieldsWhile.preserves (Property original protections)
    (fun current index initial => removed original current protections index initial)
    (fun current index old new present _ initial => updated original current protections index old new present initial)
    tree root live good

private theorem trim (original tree : BorrowTree) (protections : ProtectedTags)
    (good : Property original protections tree) :
    Property original protections {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} := by
  intro position valid
  have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  obtain ⟨before,initial,frame⟩ := good position previous
  have cache : ∀ query kind,counter
      (gc_source_trim_location tree.locations.entries[position].data).exposedCache query kind =
      counter tree.locations.entries[position].data.exposedCache query kind := by
    intro query kind
    cases kind <;> simp only [counter,GeneralBorrowGcRangeClean.trim_location_cache]
  refine ⟨before,initial,?_,?_,?_⟩
  · intro query node present
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map,GeneralBorrowGcRangeClean.trim_location_get] using frame.stored query node present
  · intro query node present kind
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map,cache] using frame.counters query node present kind
  · intro query missing kind
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map,cache] using frame.vacant query missing kind

/-- FULL production GC preserves these actual permission/cache lookup-origin
witnesses through root iteration, trimming and merging, including error states. -/
theorem collect (tree : BorrowTree) (protections : ProtectedTags) (depth : ParentDepth tree.nodes)
    (good : Every (fun location => LocationCoherent tree location protections) tree.locations)
    (live : Array BorTag) : Property tree protections (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Property tree protections) tree live (initial tree protections depth good)
  · intro current root initial
    exact children tree current protections root live initial
  · intro current initial
    exact GeneralRangeMapThoroughEvery.preserves (Witness tree protections _)
      (current.locations.modifyAll (fun _ location => gc_source_trim_location location)) (trim tree current protections initial)

end DuplicatePrefix.GeneralBorrowGcCacheFrame
