import MiriTests.Connected.Proofs.CompilerPatternDecEq219

set_option autoImplicit false

open Lean
open Miri.Input
open PatternEquality219

namespace PatternEquality219.Tests

def nestedA : CompilerPattern := .or #[.notNull, .or #[.notNull, .notNull]]
def nestedB : CompilerPattern := .or #[.notNull, .or #[.notNull, .notNull]]
def nestedReordered : CompilerPattern := .or #[.or #[.notNull, .notNull], .notNull]

theorem nestedReordered_ne : nestedA ≠ nestedReordered := by
  intro h
  have hFirst := congrArg (fun pattern : CompilerPattern =>
      match pattern with
      | .or patterns => (patterns[0]?.getD CompilerPattern.notNull)
      | _ => CompilerPattern.notNull) h
  simp [nestedA, nestedReordered] at hFirst

example : DecidableEq CompilerPattern :=
  compilerPatternDecEqInstance

example :
    (compilerPatternDecEqInstance nestedA nestedB).decide = true := by
  exact (compilerPatternDecEq_reflect nestedA nestedB).2 rfl

example :
    (compilerPatternDecEq nestedA nestedB).decide = true := by
  exact (compilerPatternDecEq_reflect nestedA nestedB).2 rfl

example :
    (compilerPatternDecEq nestedA nestedReordered).decide = false := by
  cases h : compilerPatternDecEq nestedA nestedReordered with
  | isTrue hEq => exact False.elim (nestedReordered_ne hEq)
  | isFalse _ => rfl

example (payload : Nat) :
    (compilerPatternDecEq (.range payload 0) (.range payload 0)).decide = true := by
  exact (compilerPatternDecEq_reflect _ _).2 rfl

theorem ranges_differ (leftPayload rightPayload : Nat)
    (h : leftPayload ≠ rightPayload) :
    CompilerPattern.range leftPayload 0 ≠ CompilerPattern.range rightPayload 0 := by
  intro hEq
  injection hEq with hFields
  exact h hFields

example (leftPayload rightPayload : Nat)
    (h : leftPayload ≠ rightPayload) :
    (compilerPatternDecEq (.range leftPayload 0) (.range rightPayload 0)).decide = false := by
  cases hDecision : compilerPatternDecEq (.range leftPayload 0)
      (.range rightPayload 0) with
  | isTrue hEq => exact False.elim (ranges_differ leftPayload rightPayload h hEq)
  | isFalse _ => rfl

#eval (arrayDecEqWith #[1, 2, 3] #[1, 2, 3]
  (fun (left : Nat) _ (right : Nat) _ => decEq left right)).decide
#eval (arrayDecEqWith #[1, 2, 3] #[3, 2, 1]
  (fun (left : Nat) _ (right : Nat) _ => decEq left right)).decide

end PatternEquality219.Tests

#print axioms PatternEquality219.compilerPatternDecEq
#print axioms PatternEquality219.compilerPatternDecEq_reflect
