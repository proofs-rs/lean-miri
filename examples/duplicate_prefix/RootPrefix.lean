import duplicate_prefix.RootBody
import duplicate_prefix.SourceSteps
import duplicate_prefix.CanonicalConfigFacts

/-! The first three statements of the actual reflected root body, executed by
`ExecutionMachine.step`, before any operand or pointer access. -/
namespace DuplicatePrefix.RootPrefix
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def afterStorageFrame
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (size : frame.locals.size = 25) : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 3 (by rw [size]; decide)
  let second := SourceSteps.liveFrame first ⟨0,1⟩ 4
    (by simp [first, SourceSteps.liveFrame, size])
  SourceSteps.liveFrame second ⟨0,2⟩ 5
    (by simp [second, first, SourceSteps.liveFrame, size])

theorem initial_storage [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (firstChoice secondChoice thirdChoice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (location : frame.location = .mir ⟨0,0⟩)
    (size : frame.locals.size = 25)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (dead5 : (frame.locals[5]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (trivial2 : config.lifecycle.storage.veryTriviallySized 2 = .ok true)
    (trivial0 : config.lifecycle.storage.veryTriviallySized 0 = .ok true)
    (trivial5 : config.lifecycle.storage.veryTriviallySized 5 = .ok true) :
    ∃ first second third,
      ExecutionMachine.step config limits firstChoice
        (Storage.withCurrent framesBefore frame machine) = (first,.ok true) ∧
      ExecutionMachine.step config limits secondChoice first = (second,.ok true) ∧
      ExecutionMachine.step config limits thirdChoice second = (third,.ok true) ∧
      third = Storage.withCurrent framesBefore (afterStorageFrame frame size) machine ∧
      third.machine = machine ∧
      (third.stack.currentFrame?.map (·.location)) = some (.mir ⟨0,3⟩) := by
  let block := RootBody.reflected.body.body.basicBlocks[0]'(by decide)
  let one := SourceSteps.liveFrame frame ⟨0,0⟩ 3 (by rw [size]; decide)
  have sizeOne : one.locals.size = 25 := by simp [one, SourceSteps.liveFrame, size]
  let two := SourceSteps.liveFrame one ⟨0,1⟩ 4 (by rw [sizeOne]; decide)
  have sizeTwo : two.locals.size = 25 := by simp [two, SourceSteps.liveFrame, sizeOne]
  let three := SourceSteps.liveFrame two ⟨0,2⟩ 5 (by rw [sizeTwo]; decide)
  have first := SourceSteps.storage_live_exact config limits firstChoice framesBefore frame machine
    ⟨0,0⟩ block (block.statements[0]'(by decide)) 3 2 location
    (by rw [body]; rfl) (by rfl) (by rfl) (by rw [size]; decide)
    (by rw [body]; rfl) trivial2 dead3 noClocks
  have second := SourceSteps.storage_live_exact config limits secondChoice framesBefore one machine
    ⟨0,1⟩ block (block.statements[1]'(by decide)) 4 0 (by rfl)
    (by change frame.body.basicBlocks[0]? = _; rw [body]; rfl) (by rfl) (by rfl)
    (by rw [sizeOne]; decide) (by change frame.body.locals[4]? = _; rw [body]; rfl) trivial0
    (by simpa [one, SourceSteps.liveFrame, Array.getElem_set] using dead4) (by simpa [one, SourceSteps.liveFrame] using noClocks)
  have third := SourceSteps.storage_live_exact config limits thirdChoice framesBefore two machine
    ⟨0,2⟩ block (block.statements[2]'(by decide)) 5 5 (by rfl)
    (by change frame.body.basicBlocks[0]? = _; rw [body]; rfl) (by rfl) (by rfl)
    (by rw [sizeTwo]; decide) (by change frame.body.locals[5]? = _; rw [body]; rfl) trivial5
    (by simpa [two, one, SourceSteps.liveFrame, Array.getElem_set] using dead5)
    (by simpa [two, one, SourceSteps.liveFrame] using noClocks)
  refine ⟨_,_,_,first,second,third,?_,rfl,?_⟩
  · rfl
  · simp [Storage.withCurrent, Stack.currentFrame?, three, SourceSteps.liveFrame]

theorem actual_initial_storage
    (options : Miri.Input.EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (location : frame.location = .mir ⟨0,0⟩)
    (size : frame.locals.size = 25)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (dead5 : (frame.locals[5]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    let config := PreparedContracts.actualConfig options () remaining span
    ∃ first second third,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (first,.ok true) ∧
      ExecutionMachine.step config limits () first = (second,.ok true) ∧
      ExecutionMachine.step config limits () second = (third,.ok true) ∧
      third = Storage.withCurrent framesBefore (afterStorageFrame frame size) machine ∧
      third.machine = machine ∧
      (third.stack.currentFrame?.map (·.location)) = some (.mir ⟨0,3⟩) := by
  exact initial_storage (PreparedContracts.actualConfig options () remaining span) limits () () ()
    framesBefore frame machine body location size dead3 dead4 dead5 noClocks
    (CanonicalConfigFacts.actual_storage_type2 options () remaining span)
    (CanonicalConfigFacts.actual_storage_bool options () remaining span)
    (CanonicalConfigFacts.actual_storage_usize options () remaining span)

theorem after_storage_shape
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (size : frame.locals.size = 25) :
    (afterStorageFrame frame size).body = frame.body ∧
      (afterStorageFrame frame size).bodyIdentity = frame.bodyIdentity ∧
      (afterStorageFrame frame size).functionInstance = frame.functionInstance ∧
      (afterStorageFrame frame size).extra = frame.extra ∧
      (afterStorageFrame frame size).locals.size = 25 ∧
      (afterStorageFrame frame size).location = .mir ⟨0,3⟩ := by
  simp [afterStorageFrame, SourceSteps.liveFrame, size]

theorem after_storage_slot5
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (size : frame.locals.size = 25) :
    (afterStorageFrame frame size).locals[5]'(by simp [afterStorageFrame, SourceSteps.liveFrame, size]) =
      {value := .live (.immediate .uninit), layout := (frame.locals[5]'(by omega)).layout} := by
  simp [afterStorageFrame, SourceSteps.liveFrame, Array.getElem_set]

theorem after_storage_slot4
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (size : frame.locals.size = 25) :
    (afterStorageFrame frame size).locals[4]'(by simp [afterStorageFrame, SourceSteps.liveFrame, size]) =
      {value := .live (.immediate .uninit), layout := (frame.locals[4]'(by omega)).layout} := by
  simp [afterStorageFrame, SourceSteps.liveFrame, Array.getElem_set]

theorem after_storage_slot2
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (size : frame.locals.size = 25) :
    (afterStorageFrame frame size).locals[2]'(by simp [afterStorageFrame, SourceSteps.liveFrame, size]) =
      frame.locals[2]'(by omega) := by
  simp [afterStorageFrame, SourceSteps.liveFrame, Array.getElem_set]

#print axioms actual_initial_storage

#print axioms initial_storage
end DuplicatePrefix.RootPrefix
