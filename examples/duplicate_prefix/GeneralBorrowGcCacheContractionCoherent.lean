import duplicate_prefix.GeneralBorrowGcCacheContraction
import duplicate_prefix.GeneralBorrowSparseRemoval

namespace DuplicatePrefix.GeneralBorrowGcCacheContractionCoherent
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowGcCacheContraction
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem same_sources (before after : UniValMap TreeNode)
    (oldLevels newLevels : UniIndex → TreeNode → WildcardAccessLevel) (query : UniIndex) (kind : AccessKind)
    (same : ∀ index,
      (∃ node,before.get index = some node ∧ node.isExposed = true ∧ supports (oldLevels index node) kind = true ∧
        query ∈ walk before (before.size+1) index) ↔
      (∃ node,after.get index = some node ∧ node.isExposed = true ∧ supports (newLevels index node) kind = true ∧
        query ∈ walk after (after.size+1) index)) :
    GeneralBorrowExposureCardinality.cardinality after newLevels query kind =
      GeneralBorrowExposureCardinality.cardinality before oldLevels query kind := by
  have equivalent : (GeneralBorrowExposureGraphTransport.sources after newLevels query kind).Perm
      (GeneralBorrowExposureGraphTransport.sources before oldLevels query kind) :=
    (List.perm_ext_iff_of_nodup (GeneralBorrowExposureGraphTransport.sources_nodup after newLevels query kind)
      (GeneralBorrowExposureGraphTransport.sources_nodup before oldLevels query kind)).mpr (fun index => by
        rw [GeneralBorrowExposureGraphTransport.member,GeneralBorrowExposureGraphTransport.member]
        exact (same index).symm)
  simpa only [GeneralBorrowExposureGraphTransport.sources,List.length_map,
    GeneralBorrowExposureCardinality.cardinality] using equivalent.length_eq

/-- An unexposed removed source contributes nothing. At each OTHER query,
atomic parent contraction retains the same supporting exposed descendants. -/
theorem cardinality (before after : UniValMap TreeNode) (removed : UniIndex) (node : TreeNode)
    (data : Contract before after removed node) (depth : ParentDepth before)
    (unexposed : node.isExposed = false)
    (oldLevels newLevels : UniIndex → TreeNode → WildcardAccessLevel)
    (fields : ∀ index old,before.get index = some old → index ≠ removed →
      ∃ next,after.get index = some next ∧ next.isExposed = old.isExposed ∧ newLevels index next = oldLevels index old)
    (query : UniIndex) (different : query ≠ removed) (kind : AccessKind) :
    GeneralBorrowExposureCardinality.cardinality after newLevels query kind =
      GeneralBorrowExposureCardinality.cardinality before oldLevels query kind := by
  apply same_sources
  intro index
  constructor
  · rintro ⟨old,present,exposed,supported,ancestor⟩
    have survives : index ≠ removed := by
      intro same;subst index
      have same := Option.some.inj (present.symm.trans data.present)
      subst old
      rw [unexposed] at exposed
      cases exposed
    obtain ⟨next,found,flag,level⟩ := fields index old present survives
    refine ⟨next,found,flag.trans exposed,?_,?_⟩
    · rw [level];exact supported
    · apply (walk_member data depth (before.size+1) (after.size+1) index old present survives
        (by have := depth.bounded index old present;omega)
        (by have := depth.bounded index old present;have := data.size;omega) query ?_).mpr ancestor
      exact different
  · rintro ⟨next,found,exposed,supported,ancestor⟩
    obtain ⟨survives,old,present⟩ := data.backward index next found
    obtain ⟨actual,actualFound,flag,level⟩ := fields index old present survives
    have equal := Option.some.inj (actualFound.symm.trans found)
    subst actual
    refine ⟨old,present,flag.symm.trans exposed,?_,?_⟩
    · rw [←level];exact supported
    · apply (walk_member data depth (before.size+1) (after.size+1) index old present survives
        (by have := depth.bounded index old present;omega)
        (by have := depth.bounded index old present;have := data.size;omega) query ?_).mp ancestor
      exact different

/-- Removed queries have no surviving descendant walk witness. This is derived
from actual parent presence, not assumed as a zero final-cache assertion. -/
theorem removed_zero (before after : UniValMap TreeNode) (removed : UniIndex) (node : TreeNode)
    (data : Contract before after removed node) (depth : ParentDepth before)
    (newLevels : UniIndex → TreeNode → WildcardAccessLevel) (kind : AccessKind) :
    GeneralBorrowExposureCardinality.cardinality after newLevels removed kind = 0 := by
  have absent : GeneralBorrowExposureGraphTransport.sources after newLevels removed kind = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index member
    obtain ⟨value,present,_,_,walked⟩ :=
      (GeneralBorrowExposureGraphTransport.member after newLevels removed kind index).mp member
    obtain ⟨⟨actual,lookup⟩,_⟩ := GeneralBorrowExposureAncestorDistinct.present_depth after (data.depth depth)
      (after.size+1) index value present removed walked
    rw [data.absent] at lookup
    cases lookup
  have size := congrArg List.length absent
  simpa only [GeneralBorrowExposureGraphTransport.sources,List.length_map,List.length_nil,
    GeneralBorrowExposureCardinality.cardinality] using size

/-- The exact cache deletion used by real GC preserves modular cardinality
coherence across an atomic unexposed-node contraction. No old/final support
count equation or successful GC operation is supplied as an assumption. -/
theorem coherent (before after : UniValMap TreeNode) (removed : UniIndex) (node : TreeNode)
    (data : Contract before after removed node) (depth : ParentDepth before)
    (unexposed : node.isExposed = false)
    (oldLevels newLevels : UniIndex → TreeNode → WildcardAccessLevel)
    (fields : ∀ index old,before.get index = some old → index ≠ removed →
      ∃ next,after.get index = some next ∧ next.isExposed = old.isExposed ∧ newLevels index next = oldLevels index old)
    (cache : ExposedCache) (initial : Coherent cache before oldLevels) :
    Coherent (cache.remove removed) after newLevels := by
  intro query kind
  by_cases same : query = removed
  · subst query
    rw [removed_zero before after removed node data depth newLevels kind]
    cases kind <;> simp only [counter,ExposedCache.remove,GeneralBorrowFreshDeassignment.get_removed,
      Option.getD_none]
    all_goals rfl
  · have frame : counter (cache.remove removed) query kind = counter cache query kind := by
      cases kind <;> simp only [counter,ExposedCache.remove,
        GeneralBorrowSparseRemoval.remove_get_other _ removed query same]
    rw [frame,initial query kind,cardinality before after removed node data depth unexposed oldLevels newLevels fields query same kind]

end DuplicatePrefix.GeneralBorrowGcCacheContractionCoherent
