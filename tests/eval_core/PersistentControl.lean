import Miri.Input.CompilerProviders
import Miri.Input.CompilerGlobals
import Miri.Input.InitialMachine
import Miri.Input.EvalTerminatorMachine

/-! Actual canonical World/control driver integration from an explicit isolated
post-initialization snapshot. No host poll construction or MIR stepping is
claimed by this component test. No memory/borrow/instruction hook is replaced. -/
open Miri Miri.ABI Miri.Memory Miri.Interpreter
private abbrev Host := Input.HostRuntime.Storage Unit Unit Unit Unit Unit Unit Unit Unit
private abbrev S := Input.EvalTerminatorMachine.State Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit
private def must (x : Except String A) : IO A :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
private def clockValue (s : S) : Nat :=
  match (Input.EvalTerminatorMachine.getControl s.machine.user).monotonic with
  | .virtual n => n.toNat | .host _ => 2^128
private def perform (s : S) : EStateM.Result StepError S Unit :=
  let h := Input.EvalTerminatorMachine.hooks
    (throw (.unsupported "blocking-I/O GC is an unused required host leaf in this prefix"))
  TerminatorMachine.beforeTerminatorWithChoice h (pure false) s
private def success (result : EStateM.Result StepError S Unit) : IO S :=
  match result with | .ok _ s => pure s | .error e _ => throw (IO.userError (reprStr e))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "actual compiler root JSON required")
  let decoded ← must (Input.decodeJson (← IO.FS.readFile path))
  let program ← must (Input.lowerProgram decoded.document)
  let prepared ← must (Input.CompilerProviders.prepare program)
  let dummySpan ← must (Input.CompilerContextSpan.rootSpan prepared.program)
  let definition ← must (prepared.program.rootDefinitionId 0)
  let _ ← must (Input.CallResolution.loadedBodyOfInstance prepared.lifecycle.calls.calls ⟨.Item definition,#[]⟩)
  let arrays ← must prepared.initialArrays
  let imported := Input.CompilerGlobals.importGraph prepared.runtime.target prepared.program
    (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
  let _ ← must imported.outcome
  let host : Host := {
    blocking := ⟨none,#[]⟩, clock := .virtual 0, deadlines := .empty,
    readiness := {}, futex := {}, sync := {}, io := {}, events := #[], virtualSockets := #[], tcpSockets := #[], nativeLibraries := #[], profiler := none
    control := TerminatorControl.initial ⟨10000,0x3f847ae147ae147b,true⟩ }
  let geometry ← must ((Input.InitialMachine.geometry 64 "x86_64" false none).mapError reprStr)
  let initial ← must ((Input.InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
      (H := Unit) (D := Unit) (O := Unit) (Aff := Unit) (B := Unit)
      { geometry, dummySpan, provenance := .default, addressMode := .managed
        addressStop := 18446744073709551615, addressReuse := ⟨0.5,0.1⟩
        fixedScheduling := false, trackOutdatedLoads := false, weakMemory := true
        backend := .vclocks, trackedTags := some #[], validation := .Shallow
        alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
      imported.memory arrays { inputs := #[], cursor := 0 } host).mapError reprStr)
  let initial : S := ExecutionStateTransport.inward initial
  let first ← success (perform initial)
  let second ← success (perform first)
  let control := Input.EvalTerminatorMachine.getControl second.machine.user
  check (control.basicBlockCount == 2 && control.sinceGc == 2 && clockValue second == 10000)
    "actual World counters/clock updates did not persist across two driver calls"
  check (second.machine.user.payload.payload.user.choices.cursor == 0)
    "direct explicit-choice driver unexpectedly consumed the runtime tape"
  let overflowing := {control with monotonic := .virtual (BitVec.ofNat 128 (2^128-1))}
  let badUser := Input.EvalTerminatorMachine.setControl overflowing second.machine.user
  let overflowState := {second with machine := {second.machine with user := badUser}}
  match perform overflowState with
  | .ok .. => throw (IO.userError "virtual clock checked overflow succeeded")
  | .error error failed =>
    check (error == .invalidProgram "virtual clock tick arithmetic overflow") "overflow source error category changed"
    let failedControl := Input.EvalTerminatorMachine.getControl failed.machine.user
    check (failedControl.basicBlockCount == 3 && failedControl.sinceGc == 3 && clockValue failed == 2^128-1)
      "source counter prefix/old clock lost on tick error"
  IO.println "actual World control: two persisted counter/clock transitions; checked tick error retains counter prefix; MIR EvalCore stepping remains pending"
