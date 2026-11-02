import duplicate_prefix.GeneralBorrowExposureCardinality
import duplicate_prefix.GeneralBorrowExposureAncestorDistinct
namespace DuplicatePrefix.GeneralBorrowExposurePointwise
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem point_same (cache : ExposedCache) (index : UniIndex) (before after : WildcardAccessLevel) (kind : AccessKind) :
    counter (point cache index before after) index kind = delta (counter cache index kind) (supports before kind) (supports after kind) := by
  cases kind <;> simp only [counter,point,GeneralBorrowFreshLocation.get_same,Option.getD_some,supports]

theorem point_other (cache : ExposedCache) (index query : UniIndex) (before after : WildcardAccessLevel)
    (kind : AccessKind) (different : query ≠ index) :
    counter (point cache index before after) query kind = counter cache query kind := by
  cases kind <;> simp only [counter,point,GeneralBorrowFreshLocation.get_other _ _ _ _ different]

theorem fold_absent (path : List UniIndex) (cache : ExposedCache) (query : UniIndex) (kind : AccessKind)
    (before after : WildcardAccessLevel) (absent : query ∉ path) :
    counter (path.foldl (fun current index => point current index before after) cache) query kind = counter cache query kind := by
  induction path generalizing cache with
  | nil => rfl
  | cons index rest ih =>
    have different : query ≠ index := by intro same;exact absent (by simp [same])
    have later : query ∉ rest := fun member => absent (by simp [member])
    exact (ih _ later).trans (point_other cache index query before after kind different)

/-- A distinct ancestor path applies the source delta once at members and
never at other entries, with exact UInt16 wrap retained. -/
theorem fold_counter (path : List UniIndex) (unique : path.Nodup) (cache : ExposedCache)
    (query : UniIndex) (kind : AccessKind) (before after : WildcardAccessLevel) :
    counter (path.foldl (fun current index => point current index before after) cache) query kind =
      if query ∈ path then delta (counter cache query kind) (supports before kind) (supports after kind)
      else counter cache query kind := by
  induction path generalizing cache with
  | nil => simp only [List.foldl_nil,List.not_mem_nil,ite_false]
  | cons index rest ih =>
    have tailUnique := (List.nodup_cons.mp unique).2
    by_cases same : query = index
    · subst query
      have absent := (List.nodup_cons.mp unique).1
      rw [List.foldl_cons,fold_absent rest _ index kind before after absent,point_same]
      simp only [List.mem_cons_self,ite_true]
    · rw [List.foldl_cons,ih tailUnique,point_other cache index query before after kind same]
      simp only [List.mem_cons,same,false_or]

/-- Actual arbitrary-forest updateExposure changes exactly one contributing
source at each ancestor. Completion and path distinctness are derived from raw
ParentDepth and node presence, with no operation-success premise. -/
theorem update_counter (cache : ExposedCache) (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (before after : WildcardAccessLevel) (query : UniIndex) (kind : AccessKind) :
    counter (cache.updateExposure nodes index before after).cache query kind =
      if query ∈ walk nodes (nodes.size+1) index then
        delta (counter cache query kind) (supports before kind) (supports after kind)
      else counter cache query kind := by
  rw [GeneralBorrowExposureAncestorFold.update cache nodes depth index node present before after]
  by_cases same : before = after
  · subst after
    simp only [beq_self_eq_true,ite_true]
    cases before <;> cases kind <;> simp only [supports,supportsRead,supportsWrite,delta,
      Bool.not_true,Bool.not_false,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_self]
  · have different : (before == after) = false := by simp [same]
    simp only [different,Bool.false_eq_true,ite_false]
    exact fold_counter _ (GeneralBorrowExposureAncestorDistinct.nodup nodes depth _ index node present) cache query kind before after
end DuplicatePrefix.GeneralBorrowExposurePointwise
