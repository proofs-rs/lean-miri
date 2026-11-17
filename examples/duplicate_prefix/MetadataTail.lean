import duplicate_prefix.MetadataScopedInstall
import duplicate_prefix.MetadataFinish
namespace DuplicatePrefix.MetadataTail
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open MetadataCallCore
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
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry (MetadataInstall.action h value)
  spanAt h (← h.localSpan PtrMetadataHelper.body.body 0)
  unless ← h.checkArgumentCompat () PtrMetadataHelper.abi.ret PtrMetadataHelper.abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == PtrMetadataHelper.abi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem core_eq (h : RootHooks) (value : Immediate Provenance) (destination : RuntimeStackPlace Provenance) :
    MetadataCallCore.core h ⟨.immediate value,PtrMetadataHelper.rawLayout⟩ destination = (do
      let destinationOp ← h.placeToOp () destination
      h.pushRaw () PtrMetadataHelper.resolved.callee PtrMetadataHelper.body destination (.goto (some 1) .Continue)
      action h value destinationOp) := by
  unfold MetadataCallCore.core action MetadataInstall.action
  simp only [bind_assoc]
  rfl
theorem run (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (old : Immediate Provenance) (destLayout : LocalLayout)
    (preamble : MIR.SpanRef) (located : frame.location = .unwinding preamble) (track : frame.trackCallerArg = none)
    (valid : 1 < frame.locals.size)
    (body : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead1 : frame.locals[1].value = .dead)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none) (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)
      ⟨.immediate old,destLayout⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (MetadataDone.doneFrame
        {(MetadataInstall.resultFrame frame valid (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)) with location := .unwinding preamble}) machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let value := PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let result := MetadataInstall.resultFrame frame valid value
  have same : {frame with trackCallerArg := none} = frame := by rw [←track]
  have getframe := CallEntryLocals.get_frame options limits (remaining+1) span frames frame machine
  have setframe := CallEntryLocals.set_frame options limits (remaining+1) span frames frame frame machine
  have installed := MetadataScopedInstall.install options limits remaining span debug frames frame machine tracker tracked
    carrier len valid body identity callee uncached dead1 noClocks fuel validationFuel ghost shallow
  have resultBody : result.body = PtrMetadataHelper.body.body := body
  have resultIdentity : result.bodyIdentity = PtrMetadataHelper.body.identity := identity
  have resultCallee : result.functionInstance = PtrMetadataHelper.resolved.callee := callee
  have resultValid : 0 < result.locals.size := by
    simp only [result, MetadataInstall.resultFrame,RootArgumentEntry.liveFrame, MetadataInstall.cacheFrame,
      MetadataInstall.spanFrame,LocalOperands.cachedLayoutFrame,Array.size_set]
    omega
  have resultDead : result.locals[0].value = .dead := by
    simpa [result,MetadataInstall.resultFrame,RootArgumentEntry.liveFrame,MetadataInstall.cacheFrame,
      MetadataInstall.spanFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set] using dead0
  have finished := MetadataFinish.finish options limits (remaining+1) span frames result machine preamble
    resultBody resultIdentity resultCallee resultValid resultDead noClocks
  unfold action
  simp only [bind,EStateM.bind]
  rw [getframe]
  dsimp only
  rw [located]
  simp only [pure,Pure.pure,EStateM.pure,bind,EStateM.bind]
  rw [←located,same,setframe]
  dsimp only
  rw [installed]
  change MetadataFinish.action h preamble (Storage.withCurrent frames result machine) = _
  exact finished
end
end DuplicatePrefix.MetadataTail
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.MetadataTail.core_eq, ``DuplicatePrefix.MetadataTail.run] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata tail dependency {dependency}"
