import duplicate_prefix.AsMutPtrFacts
import duplicate_prefix.SourceSteps
import duplicate_prefix.CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.AsMutPtrStorage
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
def afterStorageFrame
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (size : frame.locals.size = 5) : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 2 (by rw [size]; decide)
  let second := SourceSteps.liveFrame first ⟨0,1⟩ 3
    (by simp [first, SourceSteps.liveFrame, size])
  SourceSteps.liveFrame second ⟨0,2⟩ 4
    (by simp [second, first, SourceSteps.liveFrame, size])

theorem initial_storage [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (firstChoice secondChoice thirdChoice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (location : frame.location = .mir ⟨0,0⟩)
    (size : frame.locals.size = 5)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (trivial8 : config.lifecycle.storage.veryTriviallySized 8 = .ok true)
    (trivial204 : config.lifecycle.storage.veryTriviallySized 204 = .ok true)
 :
    ∃ first second third,
      ExecutionMachine.step config limits firstChoice
        (Storage.withCurrent framesBefore frame machine) = (first,.ok true) ∧
      ExecutionMachine.step config limits secondChoice first = (second,.ok true) ∧
      ExecutionMachine.step config limits thirdChoice second = (third,.ok true) ∧
      third = Storage.withCurrent framesBefore (afterStorageFrame frame size) machine ∧
      third.machine = machine ∧
      (third.stack.currentFrame?.map (·.location)) = some (.mir ⟨0,3⟩) := by
  let block := HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]'(by decide)
  let one := SourceSteps.liveFrame frame ⟨0,0⟩ 2 (by rw [size]; decide)
  have sizeOne : one.locals.size = 5 := by simp [one, SourceSteps.liveFrame, size]
  let two := SourceSteps.liveFrame one ⟨0,1⟩ 3 (by rw [sizeOne]; decide)
  have sizeTwo : two.locals.size = 5 := by simp [two, SourceSteps.liveFrame, sizeOne]
  let three := SourceSteps.liveFrame two ⟨0,2⟩ 4 (by rw [sizeTwo]; decide)
  have first := SourceSteps.storage_live_exact config limits firstChoice framesBefore frame machine
    ⟨0,0⟩ block (block.statements[0]'(by decide)) 2 8 location
    (by rw [body]; rfl) (by rfl) (by rfl) (by rw [size]; decide)
    (by rw [body]; rfl) trivial8 dead2 noClocks
  have second := SourceSteps.storage_live_exact config limits secondChoice framesBefore one machine
    ⟨0,1⟩ block (block.statements[1]'(by decide)) 3 204 (by rfl)
    (by change frame.body.basicBlocks[0]? = _; rw [body]; rfl) (by rfl) (by rfl)
    (by rw [sizeOne]; decide) (by change frame.body.locals[3]? = _; rw [body]; rfl) trivial204
    (by simpa [one, SourceSteps.liveFrame, Array.getElem_set] using dead3) (by simpa [one, SourceSteps.liveFrame] using noClocks)
  have third := SourceSteps.storage_live_exact config limits thirdChoice framesBefore two machine
    ⟨0,2⟩ block (block.statements[2]'(by decide)) 4 204 (by rfl)
    (by change frame.body.basicBlocks[0]? = _; rw [body]; rfl) (by rfl) (by rfl)
    (by rw [sizeTwo]; decide) (by change frame.body.locals[4]? = _; rw [body]; rfl) trivial204
    (by simpa [two, one, SourceSteps.liveFrame, Array.getElem_set] using dead4)
    (by simpa [two, one, SourceSteps.liveFrame] using noClocks)
  refine ⟨_,_,_,first,second,third,?_,rfl,?_⟩
  · rfl
  · simp [Storage.withCurrent, Stack.currentFrame?, three, SourceSteps.liveFrame]

theorem trivial_thin : CompilerStorage.veryTriviallySized PreparedReflection.actual.compiler.runtime 8 = .ok true := by decide +kernel
theorem trivial_fat : CompilerStorage.veryTriviallySized PreparedReflection.actual.compiler.runtime 204 = .ok true := by decide +kernel

theorem actual_initial_storage
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (location : frame.location = .mir ⟨0,0⟩) (size : frame.locals.size = 5)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    ∃ first second third,
      ExecutionMachine.step cfg limits () (Storage.withCurrent framesBefore frame machine) = (first,.ok true) ∧
      ExecutionMachine.step cfg limits () first = (second,.ok true) ∧
      ExecutionMachine.step cfg limits () second = (third,.ok true) ∧
      third = Storage.withCurrent framesBefore (afterStorageFrame frame size) machine ∧
      third.machine = machine ∧
      (third.stack.currentFrame?.map (·.location)) = some (.mir ⟨0,3⟩) := by
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  exact initial_storage (PreparedContracts.actualConfig options () remaining span) limits () () ()
    framesBefore frame machine body location size dead2 dead3 dead4 noClocks
    (by rw [fields.storage]; exact trivial_thin) (by rw [fields.storage]; exact trivial_fat)

open Lean Elab Command in
run_cmd do
  for declaration in [``initial_storage, ``actual_initial_storage, ``trivial_thin, ``trivial_fat] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.AsMutPtrStorage
