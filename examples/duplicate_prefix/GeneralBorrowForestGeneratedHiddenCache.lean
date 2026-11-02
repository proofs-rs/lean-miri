import duplicate_prefix.GeneralBorrowForestGeneratedProtectedReadHistory
import duplicate_prefix.GeneralBorrowRootOnlyConstructorFrames
import duplicate_prefix.GeneralBorrowGcForestCachePreservation
namespace DuplicatePrefix.GeneralBorrowForestGeneratedHiddenCache
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Hidden (tree : BorrowTree) : Prop := ∀index node,tree.nodeAt index=some node→node.isExposed=false
def Zero (location : LocationTree) : Prop := ∀query kind,counter location.exposedCache query kind=0
structure Empty (tree : BorrowTree) : Prop where
  hidden : Hidden tree
  zero : Every Zero tree.locations

theorem cardinality_zero (tree : BorrowTree) (hidden : Hidden tree) (levels : UniIndex→TreeNode→WildcardAccessLevel) (query : UniIndex) (kind : AccessKind) :
    cardinality tree.nodes levels query kind=0 := by
  have empty : tree.nodes.entries.toList.filter (contributes tree.nodes levels query kind)=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (List.mem_filter.mp member).1
    have flag := hidden row.1 row.2 present
    simpa only [contributes,flag,Bool.false_and,Bool.false_eq_true] using (List.mem_filter.mp member).2
  simp only [cardinality,empty,List.length_nil]

theorem coherent (tree : BorrowTree) (protections : ProtectedTags) (empty : Empty tree) : Every (fun location=>LocationCoherent tree location protections) tree.locations := by
  intro position valid query kind
  rw [cardinality_zero tree empty.hidden]
  exact empty.zero position valid query kind

theorem zero_of_coherent (tree : BorrowTree) (protections : ProtectedTags) (hidden : Hidden tree)
    (good : Every (fun location=>LocationCoherent tree location protections) tree.locations) : Empty tree := by
  refine ⟨hidden,?_⟩
  intro position valid query kind
  rw [good position valid query kind,cardinality_zero tree hidden]
  rfl

theorem insert_hidden (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (hidden : Hidden tree) (flag : node.isExposed=false) :
    Hidden {tree with nodes:=tree.nodes.insert index node} := by
  intro query value present
  change (tree.nodes.insert index node).get query=some value at present
  by_cases same : query=index
  · subst query;rw[GeneralBorrowFreshLocation.get_same] at present;cases present;exact flag
  · rw[GeneralBorrowFreshLocation.get_other _ index query node same] at present
    exact hidden query value present

theorem cache_shape (before after : BorrowTree)
    (same : GeneralBorrowSifaCacheFrame.cacheShape after=GeneralBorrowSifaCacheFrame.cacheShape before)
    (zero : Every Zero before.locations) : Every Zero after.locations := by
  have sizes : after.locations.entries.size=before.locations.entries.size := by
    simpa only [GeneralBorrowSifaCacheFrame.cacheShape,Array.size_map] using congrArg Array.size same
  intro position valid
  have oldValid : position<before.locations.entries.size := by omega
  have values := congrArg (fun rows=>rows[position]?) same
  simp only [GeneralBorrowSifaCacheFrame.cacheShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at values
  have cache := congrArg Prod.snd (Option.some.inj values)
  change after.locations.entries[position].data.exposedCache=before.locations.entries[position].data.exposedCache at cache
  intro query kind
  rw [cache]
  exact zero position oldValid query kind

theorem sifa (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess) (empty : Empty tree) :
    Empty (sourceUpdateSifa tree start strongest).1 := by
  refine ⟨?_,cache_shape tree _ (GeneralBorrowSifaCacheFrame.sifa_cache tree start strongest) empty.zero⟩
  intro query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure tree _ (GeneralBorrowFreshMetadataChildSifa.sifa_exposure tree start strongest) query
  rw [show (sourceUpdateSifa tree start strongest).1.nodes.get query=some node from present] at flags
  cases old : tree.nodes.get query with
  | none => simp only [old,Option.map_none,Option.map_some,reduceCtorEq] at flags
  | some before =>
    have hidden := empty.hidden query before old
    simpa only [old,Option.map_some,Option.some.injEq,hidden] using flags
end DuplicatePrefix.GeneralBorrowForestGeneratedHiddenCache
