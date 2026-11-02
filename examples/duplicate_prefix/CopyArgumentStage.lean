import duplicate_prefix.PointerArgumentCopy
import duplicate_prefix.PrimitiveArgumentCopy
import duplicate_prefix.CopyCallCore
import duplicate_prefix.CopyHelperFacts
namespace DuplicatePrefix.CopyArgumentStage
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootArgumentEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def layout (index : Fin 3) : LocalLayout :=
  if index = 0 then CopyCompilerFacts.sourcePointerLayout
  else if index = 1 then CopyCompilerFacts.destPointerLayout else RootCompilerFacts.usizeLayout

def value (source destination : Scalar Provenance) (n : UInt64) (index : Fin 3) : Immediate Provenance :=
  if index = 0 then .scalar source else if index = 1 then .scalar destination
  else .scalar (.fromScalarInt (.ofUInt64 n))

theorem cases_three (index : Fin 3) : index = 0 ∨ index = 1 ∨ index = 2 := by
  by_cases zero : index = 0
  · exact .inl zero
  by_cases one : index = 1
  · exact .inr (.inl one)
  have valZero : index.val ≠ 0 := fun h => zero (Fin.ext h)
  have valOne : index.val ≠ 1 := fun h => one (Fin.ext h)
  have valTwo : index.val = 2 := by have := index.isLt;omega
  exact .inr (.inr (Fin.ext valTwo))

theorem sized (index : Fin 3) : (layout index).layout.isSized = true := by
  rcases cases_three index with rfl | rfl | rfl <;> decide +kernel

theorem storage_trivial (index : Fin 3) : CompilerStorage.veryTriviallySized
    PreparedReflection.actual.compiler.runtime (layout index).ty = .ok true := by
  rcases cases_three index with rfl | rfl | rfl <;> decide +kernel

def resultFrame (frame : CompilerFrameContext.ActualFrame) (index : Fin 3) (valid : index.val+1 < frame.locals.size)
    (source destination : Scalar Provenance) (n : UInt64) :=
  let live := liveFrame frame (index.val+1) valid
  {live with locals := (live.locals.set (index.val+1)
    {value := .live (.immediate (value source destination n index)),layout := (live.locals[index.val+1]'(by simpa [live,liveFrame] using valid)).layout}
    (by simpa [live,liveFrame] using valid))}

theorem pass_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (index : Fin 3) (source destination : Scalar Provenance) (n : UInt64)
    (valid : index.val+1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (cached : frame.locals[index.val+1].layout = some (layout index))
    (dead : frame.locals[index.val+1].value = .dead) (noClocks : frame.extra.dataRace = none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Copy ⟨.immediate (value source destination n index),layout index⟩)
      (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret)
      (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret) index.val
      ⟨index.val+1,#[]⟩ (layout index).ty false
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (resultFrame frame index valid source destination n) machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have typed : frame.body.locals[index.val+1]? = some (layout index).ty := by
    rw [body]
    rcases cases_three index with rfl | rfl | rfl <;> with_unfolding_all rfl
  have storage := CallEntryLocals.storage_live options limits (remaining+1) span frames frame machine
    (index.val+1) (layout index).ty valid typed (storage_trivial index) dead noClocks
  have postValid : index.val+1 < (liveFrame frame (index.val+1) valid).locals.size := by simp [liveFrame];exact valid
  have postCached : (liveFrame frame (index.val+1) valid).locals[index.val+1].layout = some (layout index) := by
    simpa only [liveFrame,Array.getElem_set_self] using cached
  have evaluate := CallEntryLocals.destination_cached options limits (remaining+1) span debug frames
    (liveFrame frame (index.val+1) valid) machine (index.val+1) (layout index) postValid postCached (sized index)
  have compat : h.checkArgumentCompat ()
      (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret)
      (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    rcases cases_three index with rfl | rfl | rfl <;> with_unfolding_all rfl
  apply CallArgumentStages.copy_argument h () _ _ _ index.val ⟨index.val+1,#[]⟩ (layout index).ty _ _ _ _ _
  · change ((layout index).ty == (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret).layout.ty) = true
    rcases cases_three index with rfl | rfl | rfl <;> decide +kernel
  · change ((layout index).layout == (HelperCompilerFacts.copyAbi.args.getD index.val HelperCompilerFacts.copyAbi.ret).layout.layout) = true
    rcases cases_three index with rfl | rfl | rfl <;> decide +kernel
  · exact compat
  · rfl
  · rcases cases_three index with rfl | rfl | rfl <;> rfl
  · exact storage
  · exact evaluate
  · rcases cases_three index with rfl | rfl | rfl
    · exact PointerArgumentCopy.copy_const_pointer_argument options limits remaining span debug fuel validationFuel frames
        (liveFrame frame 1 valid) machine 1 .uninit source postValid (by simp [liveFrame]) postCached noClocks ghost shallow (LocalPlaces.localRuntimePlace frames.size (liveFrame frame 1 valid) 1 CopyCompilerFacts.sourcePointerLayout).stackView rfl
    · exact PointerArgumentCopy.copy_mut_pointer_argument options limits remaining span debug fuel validationFuel frames
        (liveFrame frame 2 valid) machine 2 .uninit destination postValid (by simp [liveFrame]) postCached noClocks ghost shallow (LocalPlaces.localRuntimePlace frames.size (liveFrame frame 2 valid) 2 CopyCompilerFacts.destPointerLayout).stackView rfl
    · exact PrimitiveArgumentCopy.copy_usize_argument options limits remaining span debug fuel validationFuel frames
        (liveFrame frame 3 valid) machine 3 .uninit n postValid (by simp [liveFrame]) postCached noClocks ghost shallow (LocalPlaces.localRuntimePlace frames.size (liveFrame frame 3 valid) 3 RootCompilerFacts.usizeLayout).stackView rfl
end
end DuplicatePrefix.CopyArgumentStage
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.CopyArgumentStage.pass_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved copy argument stage {dependency}"
