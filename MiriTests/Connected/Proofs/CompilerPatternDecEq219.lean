import Miri.Input.Model

set_option autoImplicit false

open Lean
open Miri.Input

namespace PatternEquality219

private theorem orSize (patterns : Array CompilerPattern) :
    sizeOf (CompilerPattern.or patterns) = sizeOf patterns + 1 := by
  cases patterns using Array.rec with
  | mk toList =>
    induction toList with
    | nil => rfl
    | cons head tail ih =>
      simp [sizeOf, CompilerPattern._sizeOf_1, CompilerPattern.rec_1,
        CompilerPattern.rec_2, Array._sizeOf_1, List._sizeOf_1] at *
      omega

private def listForallDec {α : Type} (p : α → Prop)
    (decideP : (x : α) → Decidable (p x)) :
    (xs : List α) → Decidable (∀ x, x ∈ xs → p x)
  | [] => isTrue (by simp)
  | x :: xs =>
    match decideP x with
    | isFalse hX => isFalse (by intro h; exact hX (h x (by simp)))
    | isTrue hX =>
      match listForallDec p decideP xs with
      | isFalse hXs =>
        isFalse (by
          intro h
          apply hXs
          intro y hY
          exact h y (by simp [hY]))
      | isTrue hXs =>
        isTrue (by
          intro y hY
          simp only [List.mem_cons] at hY
          rcases hY with hEq | hMem
          · cases hEq
            exact hX
          · exact hXs y hMem)

def arrayDecEqWith {α : Type} (left right : Array α)
    (decideElem : (leftElem : α) → leftElem ∈ left →
      (rightElem : α) → rightElem ∈ right → Decidable (leftElem = rightElem)) :
    Decidable (left = right) := by
  by_cases hSize : left.size = right.size
  · let indices := List.finRange left.size
    let rightIndex := fun i : Fin left.size => Fin.cast hSize i
    let allEqual := listForallDec
      (fun i : Fin left.size => left[i] = right[rightIndex i])
      (fun i => decideElem left[i] (Array.getElem_mem i.isLt)
        right[rightIndex i] (Array.getElem_mem (rightIndex i).isLt))
      indices
    cases allEqual with
    | isTrue hAll =>
      apply isTrue
      apply Array.ext hSize
      intro i hLeft hRight
      exact hAll ⟨i, hLeft⟩ (by simp [indices])
    | isFalse hAll =>
      apply isFalse
      intro hArray
      apply hAll
      intro i hMem
      have hGet := (Array.ext_iff.mp hArray).2 i.val i.isLt (by omega)
      simpa [rightIndex] using hGet
  · apply isFalse
    intro hArray
    exact hSize (congrArg Array.size hArray)

/-- Exact recursive comparison, with the JSON endpoint equality provided by the
caller. The array recursion uses a bounded `Fin` traversal and each recursive
pattern comparison descends to an array member. -/
def compilerPatternDecEq [DecidableEq Lean.Json] :
    (left right : CompilerPattern) → Decidable (left = right)
  | .range start finish, .range rightStart rightFinish =>
      if h : (start, finish) = (rightStart, rightFinish) then
        isTrue (by cases h; rfl)
      else
        isFalse (by intro hEq; cases hEq; exact h rfl)
  | .or leftPatterns, .or rightPatterns =>
      match arrayDecEqWith leftPatterns rightPatterns
          (fun left hLeft right hRight => compilerPatternDecEq left right) with
      | isTrue h => isTrue (congrArg CompilerPattern.or h)
      | isFalse h => isFalse (by intro hEq; injection hEq with hPatterns; exact h hPatterns)
  | .notNull, .notNull => isTrue rfl
  | .range _ _, .or _ | .range _ _, .notNull
  | .or _, .range _ _ | .or _, .notNull
  | .notNull, .range _ _ | .notNull, .or _ =>
      isFalse (by intro hEq; cases hEq)
termination_by left right => sizeOf left + sizeOf right
decreasing_by
  all_goals
    simp_wf
    have hLeftSize := Array.sizeOf_lt_of_mem hLeft
    have hRightSize := Array.sizeOf_lt_of_mem hRight
    have hLeftCtor : sizeOf leftPatterns < sizeOf (CompilerPattern.or leftPatterns) := by
      rw [orSize]
      omega
    have hRightCtor : sizeOf rightPatterns < sizeOf (CompilerPattern.or rightPatterns) := by
      rw [orSize]
      omega
    omega

/-- The decision procedure as an explicitly parameterized `DecidableEq` value.
It is intentionally not registered globally: callers choose when to install it. -/
def compilerPatternDecEqInstance [DecidableEq Lean.Json] : DecidableEq CompilerPattern :=
  compilerPatternDecEq

theorem compilerPatternDecEq_reflect [DecidableEq Lean.Json]
    (left right : CompilerPattern) :
    (compilerPatternDecEq left right).decide = true ↔ left = right := by
  cases hEq : compilerPatternDecEq left right with
  | isTrue h => simp [hEq, h]
  | isFalse h => simp [hEq, h]

end PatternEquality219

#print axioms PatternEquality219.compilerPatternDecEq

#print axioms PatternEquality219.compilerPatternDecEqInstance
