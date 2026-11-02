import duplicate_prefix.GeneralBorrowUniqueRootExposure
import duplicate_prefix.GeneralBorrowFrozenWriteExposure
namespace DuplicatePrefix.GeneralBorrowWriteCardinality
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureHistoryBounds DuplicatePrefix.GeneralBorrowFrozenWriteExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem drop_same (cache : ExposedCache) (index : UniIndex) (positive : 0 < reads cache index) :
    reads (dropRead cache index) index = reads cache index-1 := by
  simp only [reads,dropRead,GeneralBorrowFreshLocation.get_same,Option.getD_some]
  apply UInt16.toNat_sub_of_le
  change (1 : UInt16).toNat ≤ ((cache.nodes.get index).getD {}).localReads.toNat
  change 1 ≤ reads cache index
  omega

theorem drop_other (cache : ExposedCache) (index query : UniIndex) (different : query ≠ index) :
    reads (dropRead cache index) query = reads cache query := by
  simp only [reads,dropRead,GeneralBorrowFreshLocation.get_other _ _ _ _ different]

theorem drop_writes (cache : ExposedCache) (index query : UniIndex) :
    writes (dropRead cache index) query = writes cache query := by
  by_cases same : query = index
  · subst query;simp only [writes,dropRead,GeneralBorrowFreshLocation.get_same,Option.getD_some]
  · simp only [writes,dropRead,GeneralBorrowFreshLocation.get_other _ _ _ _ same]

set_option autoImplicit false in
/-- Exact remaining Read witnesses when the Unique root remains exposed. -/
structure Counts (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex) : Prop where
  rootAbsent : root ∉ leaves
  rootReads : reads cache root = leaves.length+1
  rootWrites : writes cache root = 1
  otherReads : ∀ query,query ≠ root → reads cache query = leaves.count query
  otherWrites : ∀ query,query ≠ root → writes cache query = 0

theorem root_exposed (cache : ExposedCache) (root : UniIndex) (leaves : List UniIndex)
    (good : GeneralBorrowStarExposureCounts.Counts cache root leaves) (room : leaves.length+1 < 65536) :
    Counts (GeneralBorrowUniqueRootExposure.bump cache root) root leaves := by
  obtain ⟨rootReads,rootWrites,other⟩ := GeneralBorrowUniqueRootExposure.counts cache root leaves good room
  exact ⟨good.rootAbsent,rootReads,rootWrites,fun query different => (other query different).1,
    fun query different => (other query different).2⟩

/-- A real leaf/root decrement removes exactly one witness, including when the
same leaf occurs more than once; positivity is derived from cardinality. -/
theorem step (cache : ExposedCache) (root leaf : UniIndex) (rest : List UniIndex)
    (good : Counts cache root (leaf::rest)) :
    Counts (dropRead (dropRead cache leaf) root) root rest := by
  have different : root ≠ leaf := by intro same;exact good.rootAbsent (by simp [same])
  have notRoot : leaf ≠ root := Ne.symm different
  have leafReads : reads cache leaf = rest.count leaf+1 := by
    rw [good.otherReads leaf notRoot,List.count_cons_self]
  have rootBefore : reads (dropRead cache leaf) root = rest.length+2 := by
    rw [drop_other cache leaf root different,good.rootReads]
    simp only [List.length_cons]
  refine ⟨fun member => good.rootAbsent (by simp [member]),?_,?_,?_,?_⟩
  · rw [drop_same _ root (by rw [rootBefore];omega),rootBefore];omega
  · rw [drop_writes,drop_writes,good.rootWrites]
  · intro query notRootQuery
    rw [drop_other (dropRead cache leaf) root query notRootQuery]
    by_cases same : query = leaf
    · subst query
      rw [drop_same cache leaf (by rw [leafReads];omega),leafReads];omega
    · rw [drop_other cache leaf query same,good.otherReads query notRootQuery,
        List.count_cons_of_ne (Ne.symm same)]
  · intro query notRootQuery
    rw [drop_writes,drop_writes,good.otherWrites query notRootQuery]

/-- Aggregation of the source-exact decrement deltas: after all exposed Frozen
visitors are disabled, the root alone contributes one Read and one Write. -/
theorem complete (leaves : List UniIndex) (cache : ExposedCache) (root : UniIndex)
    (good : Counts cache root leaves) :
    let final := leaves.foldl (fun cache leaf => dropRead (dropRead cache leaf) root) cache
    reads final root = 1 ∧ writes final root = 1 ∧
      ∀ query,query ≠ root → reads final query = 0 ∧ writes final query = 0 := by
  have preserve : ∀ leaves cache, Counts cache root leaves →
      Counts (leaves.foldl (fun cache leaf => dropRead (dropRead cache leaf) root) cache) root [] := by
    intro leaves
    induction leaves with
    | nil => intro cache valid;exact valid
    | cons leaf rest ih => intro cache valid;exact ih _ (step cache root leaf rest valid)
  have final := preserve leaves cache good
  refine ⟨by simpa only [List.length_nil,Nat.zero_add] using final.rootReads,final.rootWrites,?_⟩
  intro query different
  exact ⟨by simpa only [List.count_nil] using final.otherReads query different,final.otherWrites query different⟩
end DuplicatePrefix.GeneralBorrowWriteCardinality
