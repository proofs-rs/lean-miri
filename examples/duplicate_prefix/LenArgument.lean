import duplicate_prefix.LenArgumentCopy
import duplicate_prefix.LenZeroArgumentCopy
import duplicate_prefix.RootArgumentEntry
import duplicate_prefix.LenEntryFacts
namespace DuplicatePrefix.LenArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootArgumentEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem raw_storage_trivial : CompilerStorage.veryTriviallySized
    PreparedReflection.actual.compiler.runtime 7 = .ok true := by decide +kernel
theorem pass_argument_of_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance) (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (cached : frame.locals[1].layout = some LenHelper.rawLayout)
    (dead : frame.locals[1].value = .dead) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (after : CanonicalConfigFacts.RootState)
    (copy : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,LenHelper.rawLayout⟩
      (LocalPlaces.localRuntimePlace frames.size (liveFrame frame 1 valid) 1 LenHelper.rawLayout).stackView
      (Storage.withCurrent frames (liveFrame frame 1 valid) machine) = .ok () after) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.Copy ⟨.immediate value, LenHelper.rawLayout⟩)
      (LenHelper.abi.args.getD 0 LenHelper.abi.ret)
      (LenHelper.abi.args.getD 0 LenHelper.abi.ret) 0 ⟨1, #[]⟩ 7 false
      (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have typed : frame.body.locals[1]? = some 7 := by rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits (remaining + 1) span frames frame machine 1 7 valid
    typed raw_storage_trivial dead noClocks
  have postValid : 1 < (liveFrame frame 1 valid).locals.size := by simp [liveFrame]; exact valid
  have postCached : ((liveFrame frame 1 valid).locals[1]'(by simpa [liveFrame] using valid)).layout = some LenHelper.rawLayout := by
    simpa only [liveFrame, Array.getElem_set_self] using cached
  have sized : LenHelper.rawLayout.layout.isSized = true := by decide +kernel
  have evaluate := CallEntryLocals.destination_cached options limits (remaining + 1) span debug frames
    (liveFrame frame 1 valid) machine 1 LenHelper.rawLayout postValid postCached sized
  have compat : h.checkArgumentCompat () (LenHelper.abi.args.getD 0 LenHelper.abi.ret)
      (LenHelper.abi.args.getD 0 LenHelper.abi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact LenEntryFacts.argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1, #[]⟩ 7 _ _ _ _ _
  · change (7 == (LenHelper.abi.args.getD 0 LenHelper.abi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (LenHelper.rawLayout.layout == (LenHelper.abi.args.getD 0 LenHelper.abi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · exact copy

end DuplicatePrefix.LenArgument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenArgument.pass_argument_of_copy) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata argument dependency {dependency}"
