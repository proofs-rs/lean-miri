import duplicate_prefix.MemoryCopyBridge

namespace DuplicatePrefix.S04SyncSortPreserves
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
open Lean Elab in
private def helper (suffix : String) : TermElabM Expr := do
  let names := (←getEnv).constants.toList.filterMap fun (n,_) =>
    if n.toString.endsWith suffix then some n else none
  let [name] := names | throwError "expected one source helper {suffix}"
  Lean.Meta.mkConstWithFreshMVarLevels name
elab "source_partition_loop" : term => helper ".Array.qpartition.loop"
elab "source_qsort_loop" : term => helper ".Array.qsort.sort"

def All {α : Type} {n : Nat} (p : α → Prop) (xs : Vector α n) : Prop :=
  ∀ i (h : i<n), p xs[i]

theorem swap_all {α : Type} {n : Nat} (p : α → Prop) (xs : Vector α n)
    (all : All p xs) (i j : Nat) (hi : i<n) (hj : j<n) :
    All p (xs.swap i j hi hj) := by
  intro k hk
  rw [Vector.getElem_swap]
  split <;> first | exact all _ _ | (split <;> exact all _ _)

theorem partition_loop_all {α : Type} {n : Nat} (p : α → Prop)
    (lt : α → α → Bool) (lo hi : Nat) (hhi : hi<n) (pivot : α)
    (xs : Vector α n) (i k : Nat) (ilo : lo≤i) (ik : i≤k) (w : k≤hi)
    (all : All p xs) :
    All p (source_partition_loop lt lo hi hhi pivot xs i k ilo ik w).2 := by
  unfold_internal ".Array.qpartition.loop"
  split
  · split
    · apply partition_loop_all
      exact swap_all p xs all i k (by omega) (by omega)
    · exact partition_loop_all p lt lo hi hhi pivot xs i (k+1) ilo (by omega) (by omega) all
  · exact swap_all p xs all i hi (by omega) hhi
termination_by hi-k

theorem partition_all {α : Type} {n : Nat} (p : α → Prop)
    (xs : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (w : lo≤hi) (hlo : lo<n) (hhi : hi<n) (all : All p xs) :
    All p (Array.qpartition xs lt lo hi w hlo hhi).2 := by
  unfold Array.qpartition
  apply partition_loop_all
  split <;> try apply swap_all
  all_goals split <;> try apply swap_all
  all_goals split <;> try apply swap_all
  all_goals repeat apply swap_all
  all_goals exact all

theorem sort_loop_all {α : Type} {n : Nat} (p : α → Prop)
    (lt : α → α → Bool) (xs : Vector α n) (lo hi : Nat)
    (w : lo≤hi) (hlo : lo<n) (hhi : hi<n) (all : All p xs) :
    All p (source_qsort_loop lt xs lo hi w hlo hhi) := by
  unfold_internal ".Array.qsort.sort"
  split
  · cases part : Array.qpartition xs lt lo hi w hlo hhi with
    | mk mid ys =>
      cases mid with
      | mk mid bounds =>
        have ysAll : All p ys := by
          simpa only [part] using partition_all p xs lt lo hi w hlo hhi all
        dsimp only
        split
        · exact ysAll
        · apply sort_loop_all
          apply sort_loop_all
          exact ysAll
  · exact all
termination_by hi-lo
decreasing_by all_goals omega

theorem qsort_all {α : Type} (p : α → Prop) (xs : Array α)
    (lt : α → α → Bool) (all : ∀ x ∈ xs, p x) :
    ∀ x ∈ xs.qsort lt, p x := by
  have initial : All p xs.toVector := by
    intro i hi
    exact all xs[i] (Array.getElem_mem hi)
  unfold Array.qsort
  split
  · exact all
  · intro x member
    obtain ⟨i,hi,equal⟩ := Array.mem_iff_getElem.mp member
    rw [←equal]
    have hi' : i < xs.size := by simpa only [Vector.size_toArray] using hi
    exact sort_loop_all p lt xs.toVector _ _ _ _ _ initial i hi'

end DuplicatePrefix.S04SyncSortPreserves
