import duplicate_prefix.RawArgumentCopy
import duplicate_prefix.RootArgumentEntry
import duplicate_prefix.MetadataEntryFacts
namespace DuplicatePrefix.MetadataArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootArgumentEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem raw_storage_trivial : CompilerStorage.veryTriviallySized
    PreparedReflection.actual.compiler.runtime 154 = .ok true := by decide +kernel
theorem pass_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (valid : 1 < frame.locals.size)
    (body : frame.body = PtrMetadataHelper.body.body)
    (cached : frame.locals[1].layout = some PtrMetadataHelper.rawLayout)
    (dead : frame.locals[1].value = .dead) (noClocks : frame.extra.dataRace = none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel + 1)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.Copy ⟨.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len), PtrMetadataHelper.rawLayout⟩)
      (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret)
      (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret) 0 ⟨1, #[]⟩ 154 false
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames { (liveFrame frame 1 valid) with locals := ((liveFrame frame 1 valid).locals.set 1
      {value := .live (.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)),
       layout := ((liveFrame frame 1 valid).locals[1]'(by simpa [liveFrame] using valid)).layout} (by simpa [liveFrame] using valid)) } machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have typed : frame.body.locals[1]? = some 154 := by rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits (remaining + 1) span frames frame machine 1 154 valid
    typed raw_storage_trivial dead noClocks
  have postValid : 1 < (liveFrame frame 1 valid).locals.size := by simp [liveFrame]; exact valid
  have postCached : ((liveFrame frame 1 valid).locals[1]'(by simpa [liveFrame] using valid)).layout = some PtrMetadataHelper.rawLayout := by
    simpa only [liveFrame, Array.getElem_set_self] using cached
  have sized : PtrMetadataHelper.rawLayout.layout.isSized = true := by decide +kernel
  have evaluate := CallEntryLocals.destination_cached options limits (remaining + 1) span debug frames
    (liveFrame frame 1 valid) machine 1 PtrMetadataHelper.rawLayout postValid postCached sized
  have compat : h.checkArgumentCompat () (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret)
      (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact MetadataEntryFacts.argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1, #[]⟩ 154 _ _ _ _ _
  · change (154 == (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (PtrMetadataHelper.rawLayout.layout == (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · apply RawArgumentCopy.copy_raw_argument options limits remaining span debug fuel validationFuel frames
      (liveFrame frame 1 valid) machine 1 .uninit carrier len postValid (by simp [liveFrame, Array.getElem_set_self]) postCached noClocks ghost shallow _ rfl

end DuplicatePrefix.MetadataArgument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataArgument.pass_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata argument dependency {dependency}"
