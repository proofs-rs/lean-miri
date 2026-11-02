import duplicate_prefix.CallArgumentStages
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.PositiveReferenceArgumentCopy

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.RootArgumentEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

noncomputable def liveFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (id : MIR.LocalId) (valid : id < frame.locals.size) :=
  {frame with locals := (frame.locals.set id
    {value := .live (.immediate .uninit), layout := frame.locals[id].layout} valid)}

/-- Internal source composition. The copy stage is discharged by the actual
reference/usize argument-copy theorems before a complete-entry theorem is used. -/
theorem pass1_of_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance) (valid : 1 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (cached : frame.locals[1].layout = some RootCompilerFacts.sliceLayout)
    (dead : frame.locals[1].value = .dead) (noClocks : frame.extra.dataRace = none)
    (after : CanonicalConfigFacts.RootState)
    (copy : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).copyAllowTransmute ()
      ⟨.immediate value, RootCompilerFacts.sliceLayout⟩
      (LocalPlaces.localRuntimePlace frames.size (liveFrame frame 1 valid) 1 RootCompilerFacts.sliceLayout).stackView
      (Storage.withCurrent frames (liveFrame frame 1 valid) machine) = .ok () after) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.Copy ⟨.immediate value, RootCompilerFacts.sliceLayout⟩)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret) 0 ⟨1, #[]⟩ 3 false
      (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have typed : frame.body.locals[1]? = some 3 := by rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits remaining span frames frame machine 1 3 valid
    typed RootCompilerFacts.root_storage_trivial_slice dead noClocks
  have postValid : 1 < (liveFrame frame 1 valid).locals.size := by simp [liveFrame]; exact valid
  have postCached : (liveFrame frame 1 valid).locals[1].layout = some RootCompilerFacts.sliceLayout := by
    simpa only [liveFrame, Array.getElem_set_self] using cached
  have sized : RootCompilerFacts.sliceLayout.layout.isSized = true := by decide +kernel
  have evaluate := CallEntryLocals.destination_cached options limits remaining span debug frames
    (liveFrame frame 1 valid) machine 1 RootCompilerFacts.sliceLayout postValid postCached sized
  have compat : h.checkArgumentCompat () (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact CallEntryFacts.root_slice_argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1, #[]⟩ 3 _ _ _ after _
  · change (3 == (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (RootCompilerFacts.sliceLayout.layout == (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · exact copy

/-- Internal source composition. The copy stage is discharged by the actual
reference/usize argument-copy theorems before a complete-entry theorem is used. -/
theorem pass2_of_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance) (valid : 2 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (cached : frame.locals[2].layout = some RootCompilerFacts.usizeLayout)
    (dead : frame.locals[2].value = .dead) (noClocks : frame.extra.dataRace = none)
    (after : CanonicalConfigFacts.RootState)
    (copy : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).copyAllowTransmute ()
      ⟨.immediate value, RootCompilerFacts.usizeLayout⟩
      (LocalPlaces.localRuntimePlace frames.size (liveFrame frame 2 valid) 2 RootCompilerFacts.usizeLayout).stackView
      (Storage.withCurrent frames (liveFrame frame 2 valid) machine) = .ok () after) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.Copy ⟨.immediate value, RootCompilerFacts.usizeLayout⟩)
      (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret) 1 ⟨2, #[]⟩ 5 false
      (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have typed : frame.body.locals[2]? = some 5 := by rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits remaining span frames frame machine 2 5 valid
    typed RootCompilerFacts.root_storage_trivial_usize dead noClocks
  have postValid : 2 < (liveFrame frame 2 valid).locals.size := by simp [liveFrame]; exact valid
  have postCached : (liveFrame frame 2 valid).locals[2].layout = some RootCompilerFacts.usizeLayout := by
    simpa only [liveFrame, Array.getElem_set_self] using cached
  have sized : RootCompilerFacts.usizeLayout.layout.isSized = true := by decide +kernel
  have evaluate := CallEntryLocals.destination_cached options limits remaining span debug frames
    (liveFrame frame 2 valid) machine 2 RootCompilerFacts.usizeLayout postValid postCached sized
  have compat : h.checkArgumentCompat () (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact CallEntryFacts.root_usize_argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 1 ⟨2, #[]⟩ 5 _ _ _ after _
  · change (5 == (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (RootCompilerFacts.usizeLayout.layout == (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · exact copy

end DuplicatePrefix.RootArgumentEntry
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootArgumentEntry.pass1_of_copy,
      ``DuplicatePrefix.RootArgumentEntry.pass2_of_copy] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root argument composition dependency {dependency}"
