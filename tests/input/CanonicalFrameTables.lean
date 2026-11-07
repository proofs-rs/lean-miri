import Miri.Input.CompilerFrameContext
import Miri.Input.Decoder

open Miri Miri.Input Miri.Interpreter Miri.MIR Miri.Memory

example (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (tables : SyntaxTables) :
    (CompilerFrameContext.canonicalFrame p {frame with mirTables := tables}).instruction? =
      (CompilerFrameContext.canonicalFrame p frame).instruction? := rfl

example (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (tables : SyntaxTables) :
    (CompilerFrameContext.canonicalFrame p {frame with mirTables := tables}).currentSpan =
      (CompilerFrameContext.canonicalFrame p frame).currentSpan := rfl

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def check (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw (IO.userError reason)
private def state (frame : CompilerFrameContext.ActualFrame) : MachineHooks.State Unit Unit :=
  ⟨⟨#[frame]⟩,⟨MemoryState.empty,none,none,⟨.MAIN_THREAD,[],[],false,false⟩,#[],#[],()⟩⟩
private def result {α : Type} (action : MachineHooks.M Unit Unit α)
    (frame : CompilerFrameContext.ActualFrame) : Except StepError α :=
  match action.run (state frame) with
  | .ok value _ => .ok value
  | .error reason _ => .error reason

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected current exporter fixture")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let p ← must (CompilerProviders.prepare (← must (lowerCoreProgram decoded.document)))
  let some row := p.lifecycle.calls.calls.bodies[0]? | throw (IO.userError "fixture has no body")
  let loaded ← must (CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls row.fnInstance)
  let some ty := loaded.body.locals[0]? | throw (IO.userError "fixture lacks return local")
  let layout ← must ((p.runtime.lookup ty).mapError toString)
  let identity := LocalsIdentity.ofAllocationToken 0
  let frame : CompilerFrameContext.ActualFrame :=
    {Frame.create loaded row.fnInstance ⟨none,none,0,none⟩ (.stop true)
      (.frameLocal 0 0 none layout identity) ⟨0⟩ identity with location := .mir .start}
  let forged := {frame with mirTables := {}}
  check (!forged.instruction?.isOk) "empty execution table unexpectedly provided an instruction"
  let expected := result (CompilerFrameContext.instruction p) frame
  check expected.isOk "canonical instruction query failed"
  check (decide (expected = frame.instruction?.mapError StepError.stack))
    "canonical instruction changed the ordinary loaded-frame observation"
  check (decide (result (CompilerFrameContext.instruction p) forged = expected))
    "compiler instruction trusted the forged frame table"
  let span := result (CompilerFrameContext.currentSpan p) frame
  check span.isOk "canonical span query failed"
  check (decide (span = frame.currentSpan.mapError StepError.stack))
    "canonical span changed the ordinary loaded-frame observation"
  check (decide (result (CompilerFrameContext.currentSpan p) forged = span))
    "compiler span trusted the forged frame table"
  let badId := {forged with bodyId := ⟨p.program.input.mirTables.mir.bodies.size⟩}
  check (!(result (CompilerFrameContext.instruction p) badId).isOk)
    "canonical body ID mismatch was accepted"
  IO.println "canonical compiler instruction/span ignore forged frame tables; identity guards remain checked: PASS"
