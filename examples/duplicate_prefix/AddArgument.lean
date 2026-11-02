import duplicate_prefix.PointerArgumentCopy
import duplicate_prefix.RootArgumentEntry
import duplicate_prefix.AddEntryFacts
namespace DuplicatePrefix.AddArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootArgumentEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem raw_storage_trivial : CompilerStorage.veryTriviallySized
    PreparedReflection.actual.compiler.runtime 8 = .ok true := by decide +kernel
theorem pass_pointer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Scalar Provenance) (valid : 1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (cached : frame.locals[1].layout = some CopyCompilerFacts.destPointerLayout)
    (dead : frame.locals[1].value = .dead) (noClocks : frame.extra.dataRace = none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel + 1)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.Copy ⟨.immediate (.scalar pointer), CopyCompilerFacts.destPointerLayout⟩)
      (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret) 0 ⟨1, #[]⟩ 8 false
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames { (liveFrame frame 1 valid) with locals := ((liveFrame frame 1 valid).locals.set 1
      {value := .live (.immediate (.scalar pointer)),
       layout := ((liveFrame frame 1 valid).locals[1]'(by simpa [liveFrame] using valid)).layout} (by simpa [liveFrame] using valid)) } machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have typed : frame.body.locals[1]? = some 8 := by rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits (remaining + 1) span frames frame machine 1 8 valid
    typed raw_storage_trivial dead noClocks
  have postValid : 1 < (liveFrame frame 1 valid).locals.size := by simp [liveFrame]; exact valid
  have postCached : ((liveFrame frame 1 valid).locals[1]'(by simpa [liveFrame] using valid)).layout = some CopyCompilerFacts.destPointerLayout := by
    simpa only [liveFrame, Array.getElem_set_self] using cached
  have sized : CopyCompilerFacts.destPointerLayout.layout.isSized = true := by decide +kernel
  have evaluate := CallEntryLocals.destination_cached options limits (remaining + 1) span debug frames
    (liveFrame frame 1 valid) machine 1 CopyCompilerFacts.destPointerLayout postValid postCached sized
  have compat : h.checkArgumentCompat () (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact AddEntryFacts.argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1, #[]⟩ 8 _ _ _ _ _
  · change (8 == (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (CopyCompilerFacts.destPointerLayout.layout == (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · apply PointerArgumentCopy.copy_mut_pointer_argument options limits remaining span debug fuel validationFuel frames
      (liveFrame frame 1 valid) machine 1 .uninit pointer postValid (by simp [liveFrame, Array.getElem_set_self]) postCached noClocks ghost shallow _ rfl

theorem pass_usize
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64) (valid : 2 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (cached : frame.locals[2].layout = some RootCompilerFacts.usizeLayout)
    (dead : frame.locals[2].value = .dead) (noClocks : frame.extra.dataRace = none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel + 1)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      (.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩)
      (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret) 1 ⟨2, #[]⟩ 5 false
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames { (liveFrame frame 2 valid) with locals := ((liveFrame frame 2 valid).locals.set 2
      {value := .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),
       layout := ((liveFrame frame 2 valid).locals[2]'(by simpa [liveFrame] using valid)).layout} (by simpa [liveFrame] using valid)) } machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have typed : frame.body.locals[2]? = some 5 := by rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits (remaining + 1) span frames frame machine 2 5 valid
    typed RootCompilerFacts.root_storage_trivial_usize dead noClocks
  have postValid : 2 < (liveFrame frame 2 valid).locals.size := by simp [liveFrame]; exact valid
  have postCached : ((liveFrame frame 2 valid).locals[2]'(by simpa [liveFrame] using valid)).layout = some RootCompilerFacts.usizeLayout := by
    simpa only [liveFrame, Array.getElem_set_self] using cached
  have sized : RootCompilerFacts.usizeLayout.layout.isSized = true := by decide +kernel
  have evaluate := CallEntryLocals.destination_cached options limits (remaining + 1) span debug frames
    (liveFrame frame 2 valid) machine 2 RootCompilerFacts.usizeLayout postValid postCached sized
  have compat : h.checkArgumentCompat () (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact AddEntryFacts.argument1_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 1 ⟨2, #[]⟩ 5 _ _ _ _ _
  · change (5 == (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (RootCompilerFacts.usizeLayout.layout == (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · apply PrimitiveArgumentCopy.copy_usize_argument options limits remaining span debug fuel validationFuel frames
      (liveFrame frame 2 valid) machine 2 .uninit n postValid (by simp [liveFrame, Array.getElem_set_self]) postCached noClocks ghost shallow _ rfl

end DuplicatePrefix.AddArgument
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddArgument.pass_pointer, ``DuplicatePrefix.AddArgument.pass_usize] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata argument dependency {dependency}"
