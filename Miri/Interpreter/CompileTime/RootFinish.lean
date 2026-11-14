import Lean

/-! Control from pinned eval_queries.rs::intern_and_validate (8144389c895d).
Interning's Result is deferred, while its World effects commit immediately.
Validation can override that deferred failure. Diagnostic production and root
conversion remain callbacks; no compiler allocation or query result is supplied.
Root is opaque and is passed unchanged to each root-sensitive callback. -/
namespace Miri.Interpreter.CompileTime.RootFinish
inductive InternError where
  | badMutablePointer | danglingPointer | constAllocNotGlobal | partialPointer
  deriving Repr, DecidableEq
inductive Stage where
  | validation | interningReport
  deriving Repr, DecidableEq
inductive Result (World Error Value : Type) where
  | returned (value : Value) (world : World)
  | failed (stage : Stage) (error : Error) (world : World)
  deriving Repr, DecidableEq

set_option autoImplicit false in
def finish {Root World Error Value : Type}
    (intern : Root → World → Except InternError Unit × World)
    (validate : Root → World → Except Error Unit × World)
    (report : InternError → World → Error × World)
    (makeResult : Root → World → Value × World)
    (root : Root) (world : World) : Result World Error Value :=
  let (deferred,world) := intern root world
  let (validated,world) := validate root world
  match validated with
  | .error error => .failed .validation error world
  | .ok () => match deferred with
    | .error error =>
      let (error,world) := report error world
      .failed .interningReport error world
    | .ok () =>
      let (value,world) := makeResult root world
      .returned value world

set_option autoImplicit false in
/-- A validation error wins over either interning result. Effects from both
callbacks remain in the returned World, and no deferred report/result runs. -/
theorem validationFailureWins {Root World Error Value : Type}
    (intern : Root → World → Except InternError Unit × World)
    (validate : Root → World → Except Error Unit × World)
    (report : InternError → World → Error × World)
    (makeResult : Root → World → Value × World)
    (root : Root) (world₀ world₁ world₂ : World)
    (deferred : Except InternError Unit) (error : Error)
    (hi : intern root world₀ = (deferred,world₁))
    (hv : validate root world₁ = (.error error,world₂)) :
    finish intern validate report makeResult root world₀ = .failed .validation error world₂ := by
  unfold finish
  rw [hi]
  dsimp only
  rw [hv]

set_option autoImplicit false in
/-- Deferred interning errors are reported only after successful validation. -/
theorem deferredInterningFailure {Root World Error Value : Type}
    (intern : Root → World → Except InternError Unit × World)
    (validate : Root → World → Except Error Unit × World)
    (report : InternError → World → Error × World)
    (makeResult : Root → World → Value × World)
    (root : Root) (world₀ world₁ world₂ world₃ : World)
    (internError : InternError) (error : Error)
    (hi : intern root world₀ = (.error internError,world₁))
    (hv : validate root world₁ = (.ok (),world₂))
    (hr : report internError world₂ = (error,world₃)) :
    finish intern validate report makeResult root world₀ = .failed .interningReport error world₃ := by
  unfold finish
  rw [hi]
  dsimp only
  rw [hv]
  dsimp only
  rw [hr]

set_option autoImplicit false in
/-- Success constructs the result only after both stages, using the same root. -/
theorem successfulFinish {Root World Error Value : Type}
    (intern : Root → World → Except InternError Unit × World)
    (validate : Root → World → Except Error Unit × World)
    (report : InternError → World → Error × World)
    (makeResult : Root → World → Value × World)
    (root : Root) (world₀ world₁ world₂ world₃ : World) (value : Value)
    (hi : intern root world₀ = (.ok (),world₁))
    (hv : validate root world₁ = (.ok (),world₂))
    (hm : makeResult root world₂ = (value,world₃)) :
    finish intern validate report makeResult root world₀ = .returned value world₃ := by
  unfold finish
  rw [hi]
  dsimp only
  rw [hv]
  dsimp only
  rw [hm]

end Miri.Interpreter.CompileTime.RootFinish
