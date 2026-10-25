import Miri.Input.EvalMiriHostEffectsConstruction

open Miri.Input.EvalMiriHostEffectsConstruction Miri.Interpreter

private structure Trace where
  calls : Array ByteArray := #[]
  answers : Array (Except StepError (Except (IoError.HostError Unit) Nat)) := #[]
  cursor : Nat := 0

private def scriptedWrite (bytes : ByteArray) : EStateM StepError Trace
    (Except (IoError.HostError Unit) Nat) := do
  let state ← get
  let some answer := state.answers[state.cursor]? |
    throw (.invalidProgram "write_all made an unplanned host call")
  set {state with calls := state.calls.push bytes, cursor := state.cursor + 1}
  match answer with
  | .ok result => pure result
  | .error error => throw error

private def hostError (kind : IoError.ErrorKind) : IoError.HostError Unit :=
  ⟨kind, none, ()⟩

private def runCase (budget : Nat)
    (answers : Array (Except StepError (Except (IoError.HostError Unit) Nat))) :=
  writeAllHost scriptedWrite budget (ByteArray.mk #[10,20,30])
    (⟨#[], answers, 0⟩ : Trace)

def main : IO Unit := do
  let full := ByteArray.mk #[10,20,30]
  let tail := ByteArray.mk #[20,30]
  match runCase 2 #[.ok (.ok 1), .ok (.ok 2)] with
  | .ok () state =>
    unless state.calls == #[full,tail] && state.cursor == 2 do
      throw (IO.userError "short-write retry did not advance by returned count")
  | .error error _ => throw (IO.userError s!"short-write retry failed: {reprStr error}")
  match runCase 2 #[.ok (.error (hostError .Interrupted)), .ok (.ok 3)] with
  | .ok () state =>
    unless state.calls == #[full,full] && state.cursor == 2 do
      throw (IO.userError "Interrupted retry did not resend unchanged bytes")
  | .error error _ => throw (IO.userError s!"Interrupted retry failed: {reprStr error}")
  match runCase 1 #[.ok (.error (hostError .BrokenPipe))] with
  | .ok () state =>
    unless state.calls == #[full] do
      throw (IO.userError "ordinary host error caused an extra write")
  | .error error _ => throw (IO.userError s!"ordinary host error escaped: {reprStr error}")
  match runCase 1 #[.ok (.ok 0)] with
  | .ok () state =>
    unless state.calls == #[full] do
      throw (IO.userError "zero progress caused an extra write")
  | .error error _ => throw (IO.userError s!"zero-progress host result escaped: {reprStr error}")
  match runCase 1 #[.ok (.ok 4)] with
  | .error (.invalidProgram _) state =>
    unless state.calls == #[full] do
      throw (IO.userError "impossible count lost the host call")
  | _ => throw (IO.userError "impossible host count was accepted")
  match runCase 1 #[.ok (.ok 1)] with
  | .error (.resourceExhaustion _) state =>
    unless state.calls == #[full] do
      throw (IO.userError "budget exhaustion lost the partial write")
  | _ => throw (IO.userError "incomplete write exhausted no budget")
  match runCase 1 #[.error (.unsupported "missing host capability")] with
  | .error (.unsupported _) state =>
    unless state.calls == #[full] do
      throw (IO.userError "missing capability lost the host call")
  | _ => throw (IO.userError "missing host capability was ignored")
  IO.println "Miri write_all host retry PASS: short, Interrupted, host error, zero, impossible, budget, capability"
