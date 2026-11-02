import Miri.Interpreter.RunLoop

/-! Executable host control for the fixed interpreter step. The proof-facing
finite runner and step semantics remain separate. This loop has no implicit
iteration limit: only a step error/termination or an explicitly requested
bounded diagnostic run stops it. -/
namespace Miri.Interpreter.NativeRunLoop

inductive Result (S : Type) where
  | stopped (state : S) (error : StepError) (iterations : Nat)
  | exhausted (state : S) (iterations : Nat)
  deriving Repr

private partial def loop {S : Type} [Nonempty (Result S)]
    (step : Nat → S → StepResult S Unit) (limit : Option Nat)
    (iterations : Nat) (state : S) : Result S :=
  if limit.any (iterations >= ·) then .exhausted state iterations
  else
    let (after, result) := step iterations state
    match result with
    | .error error => .stopped after error (iterations + 1)
    | .ok () => loop step limit (iterations + 1) after

/-- No successful process outcome can be fabricated by exhausting a bound.
The supplied step is the fixed RunLoop.iteration at source assembly call sites.
Nonempty is proof-erased; it does not retain an initial-world runtime copy. -/
def run {S : Type} (step : Nat → S → StepResult S Unit)
    (limit : Option Nat) (initial : S) : Result S :=
  letI : Nonempty (Result S) := ⟨.exhausted initial 0⟩
  loop step limit 0 initial

end Miri.Interpreter.NativeRunLoop
