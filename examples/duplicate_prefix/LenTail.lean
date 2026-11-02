import duplicate_prefix.LenPositiveInstall
import duplicate_prefix.LenFinish
namespace DuplicatePrefix.LenTail
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open LenCallCore
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def action (h : RootHooks) (value : Immediate Provenance) (destinationOp : OpTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry (LenInstall.action h value)
  spanAt h (← h.localSpan LenHelper.body.body 0)
  unless ← h.checkArgumentCompat () LenHelper.abi.ret LenHelper.abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == LenHelper.abi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem core_eq (h : RootHooks) (value : Immediate Provenance) (destination : RuntimeStackPlace Provenance) :
    LenCallCore.core h ⟨.immediate value,LenHelper.rawLayout⟩ destination = (do
      let destinationOp ← h.placeToOp () destination
      h.pushRaw () LenHelper.resolved.callee LenHelper.body destination (.goto (some 3) .Continue)
      action h value destinationOp) := by
  unfold LenCallCore.core action LenInstall.action
  simp only [bind_assoc]
  rfl
theorem run_of_install (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value old : Immediate Provenance) (destLayout : LocalLayout)
    (preamble : MIR.SpanRef) (located : frame.location = .unwinding preamble) (track : frame.trackCallerArg = none)
    (afterFrame : CompilerFrameContext.ActualFrame) (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (installed : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) = .ok (1,1) (Storage.withCurrent frames afterFrame afterMachine))
    (body : afterFrame.body = LenHelper.body.body)
    (identity : afterFrame.bodyIdentity = LenHelper.body.identity)
    (callee : afterFrame.functionInstance = LenHelper.resolved.callee)
    (valid : 0 < afterFrame.locals.size) (dead0 : afterFrame.locals[0].value = .dead)
    (noClocks : afterFrame.extra.dataRace = none) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      ⟨.immediate old,destLayout⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (LenDone.doneFrame {afterFrame with location := .unwinding preamble}) afterMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have same : {frame with trackCallerArg := none} = frame := by rw [←track]
  have getframe := CallEntryLocals.get_frame options limits (remaining+1) span frames frame machine
  have setframe := CallEntryLocals.set_frame options limits (remaining+1) span frames frame frame machine
  have finished := LenFinish.finish options limits (remaining+1) span frames afterFrame afterMachine preamble
    body identity callee valid dead0 noClocks
  unfold action
  simp only [bind,EStateM.bind]
  rw [getframe]
  dsimp only
  rw [located]
  simp only [pure,Pure.pure,EStateM.pure,bind,EStateM.bind]
  rw [←located,same,setframe]
  dsimp only
  rw [installed]
  change LenFinish.action h preamble (Storage.withCurrent frames afterFrame afterMachine) = _
  exact finished

end
end DuplicatePrefix.LenTail
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LenTail.core_eq, ``DuplicatePrefix.LenTail.run_of_install] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata tail dependency {dependency}"
