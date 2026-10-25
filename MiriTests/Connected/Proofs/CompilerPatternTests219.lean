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

example [DecidableEq Lean.Json] : DecidableEq CompilerPattern :=
  compilerPatternDecEqInstance

example [DecidableEq Lean.Json] :
    (compilerPatternDecEqInstance nestedA nestedB).decide = true := by
  exact (compilerPatternDecEq_reflect nestedA nestedB).2 rfl

example [DecidableEq Lean.Json] :
    (compilerPatternDecEq nestedA nestedB).decide = true := by
  exact (compilerPatternDecEq_reflect nestedA nestedB).2 rfl

example [DecidableEq Lean.Json] :
    (compilerPatternDecEq nestedA nestedReordered).decide = false := by
  cases h : compilerPatternDecEq nestedA nestedReordered with
  | isTrue hEq => exact False.elim (nestedReordered_ne hEq)
  | isFalse _ => rfl

example [DecidableEq Lean.Json] (payload : Lean.Json) :
    (compilerPatternDecEq (.range payload .null) (.range payload .null)).decide = true := by
  exact (compilerPatternDecEq_reflect _ _).2 rfl

theorem ranges_differ (leftPayload rightPayload : Lean.Json)
    (h : leftPayload ≠ rightPayload) :
    CompilerPattern.range leftPayload .null ≠ CompilerPattern.range rightPayload .null := by
  intro hEq
  injection hEq with hFields
  exact h hFields

example [DecidableEq Lean.Json] (leftPayload rightPayload : Lean.Json)
    (h : leftPayload ≠ rightPayload) :
    (compilerPatternDecEq (.range leftPayload .null) (.range rightPayload .null)).decide = false := by
  cases hDecision : compilerPatternDecEq (.range leftPayload .null)
      (.range rightPayload .null) with
  | isTrue hEq => exact False.elim (ranges_differ leftPayload rightPayload h hEq)
  | isFalse _ => rfl

#eval (arrayDecEqWith #[1, 2, 3] #[1, 2, 3]
  (fun (left : Nat) _ (right : Nat) _ => decEq left right)).decide
#eval (arrayDecEqWith #[1, 2, 3] #[3, 2, 1]
  (fun (left : Nat) _ (right : Nat) _ => decEq left right)).decide

end PatternEquality219.Tests

#print axioms PatternEquality219.compilerPatternDecEq
#print axioms PatternEquality219.compilerPatternDecEq_reflect
