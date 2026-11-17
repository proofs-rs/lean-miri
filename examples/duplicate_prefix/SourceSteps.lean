import duplicate_prefix.Storage
import duplicate_prefix.StepFacts
import duplicate_prefix.StepAssembly
import Miri.Interpreter.ExecutionMachine

/-! Statement effects connected to the actual canonical MIR step assembly. -/

namespace DuplicatePrefix.SourceSteps
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def liveFrame
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (location : Location) (localId : LocalId) (valid : localId < frame.locals.size) :=
  {frame with
    locals := (frame.locals.set localId
      {value := .live (.immediate .uninit), layout := frame.locals[localId].layout} valid)
    location := .mir {location with statementIndex := location.statementIndex+1}}

theorem storage_live_exact [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (location : Location) (block : BasicBlock) (statement : Statement)
    (localId : LocalId) (ty : TyId)
    (frameLocation : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (statementAt : block.statements[location.statementIndex]? = some statement)
    (statementKind : statement.kind = .StorageLive localId)
    (valid : localId < frame.locals.size)
    (typed : frame.body.locals[localId]? = some ty)
    (trivial : config.lifecycle.storage.veryTriviallySized ty = .ok true)
    (dead : frame.locals[localId].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    ExecutionMachine.step config limits choice (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore (liveFrame frame location localId valid) machine, .ok true) := by
  let updatedFrame := { frame with locals := (frame.locals.set localId
    { value := .live (.immediate .uninit), layout := frame.locals[localId].layout } valid) }
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  have effect : Step.evalStatement (ExecutionMachine.stepHooks config limits) choice statement
      (Storage.withCurrent framesBefore frame machine) = (updated, .ok ()) := by
    unfold Step.evalStatement
    rw [statementKind]
    change MachineHooks.run (MachineHooks.storageLiveDyn config.lifecycle.storage localId .none)
      (Storage.withCurrent framesBefore frame machine) = _
    unfold MachineHooks.run Call.run
    rw [Storage.storage_live_dead config.lifecycle.storage framesBefore frame machine localId ty
      valid typed trivial dead noClocks]
  have step := StepFacts.step_statement (ExecutionMachine.stepHooks config limits) choice
    (Storage.withCurrent framesBefore frame machine) updated frame updatedFrame location location
    block statement (by simp [Storage.withCurrent, Stack.currentFrame?]) frameLocation blockAt
    statementAt effect (by simp [updated, Storage.withCurrent])
    (by simp [updated, Storage.withCurrent, Stack.currentFrame?])
    (by simpa [updatedFrame] using frameLocation) (by simp [updated, Storage.withCurrent])
  simpa [ExecutionMachine.step, liveFrame, updated, updatedFrame, Storage.withCurrent, Array.set_push] using step

def deadFrame
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (location : Location) (localId : LocalId) (valid : localId < frame.locals.size) :=
  {frame with
    locals := (frame.locals.set localId
      {value := .dead, layout := frame.locals[localId].layout} valid)
    location := .mir {location with statementIndex := location.statementIndex+1}}

theorem storage_dead_exact [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (location : Location) (block : BasicBlock) (statement : Statement)
    (localId : LocalId) (immediate : Immediate Provenance)
    (frameLocation : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (statementAt : block.statements[location.statementIndex]? = some statement)
    (statementKind : statement.kind = .StorageDead localId)
    (valid : localId < frame.locals.size)
    (notReturn : localId ≠ 0)
    (live : frame.locals[localId].value = .live (.immediate immediate)) :
    ExecutionMachine.step config limits choice (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore (deadFrame frame location localId valid) machine, .ok true) := by
  let updatedFrame := { frame with locals := (frame.locals.set localId
    { value := .dead, layout := frame.locals[localId].layout } valid) }
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  have effect : Step.evalStatement (ExecutionMachine.stepHooks config limits) choice statement
      (Storage.withCurrent framesBefore frame machine) = (updated, .ok ()) := by
    unfold Step.evalStatement
    rw [statementKind]
    change MachineHooks.run (MachineHooks.storageDead config.lifecycle.storage localId)
      (Storage.withCurrent framesBefore frame machine) = _
    unfold MachineHooks.run Call.run
    rw [Storage.storage_dead_immediate config.lifecycle.storage framesBefore frame machine localId immediate
      valid notReturn live]
  have step := StepFacts.step_statement (ExecutionMachine.stepHooks config limits) choice
    (Storage.withCurrent framesBefore frame machine) updated frame updatedFrame location location
    block statement (by simp [Storage.withCurrent, Stack.currentFrame?]) frameLocation blockAt
    statementAt effect (by simp [updated, Storage.withCurrent])
    (by simp [updated, Storage.withCurrent, Stack.currentFrame?])
    (by simpa [updatedFrame] using frameLocation) (by simp [updated, Storage.withCurrent])
  simpa [ExecutionMachine.step, deadFrame, updated, updatedFrame, Storage.withCurrent, Array.set_push] using step

theorem storage_live_step [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (location : Location) (block : BasicBlock) (statement : Statement)
    (localId : LocalId) (ty : TyId)
    (frameLocation : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (statementAt : block.statements[location.statementIndex]? = some statement)
    (statementKind : statement.kind = .StorageLive localId)
    (valid : localId < frame.locals.size)
    (typed : frame.body.locals[localId]? = some ty)
    (trivial : config.lifecycle.storage.veryTriviallySized ty = .ok true)
    (dead : frame.locals[localId].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    ∃ after, ExecutionMachine.step config limits choice
        (Storage.withCurrent framesBefore frame machine) = (after, .ok true) ∧
      after.machine = machine := by
  let updatedFrame := { frame with locals := (frame.locals.set localId
    { value := .live (.immediate .uninit), layout := frame.locals[localId].layout } valid) }
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  have effect : Step.evalStatement (ExecutionMachine.stepHooks config limits) choice statement
      (Storage.withCurrent framesBefore frame machine) = (updated, .ok ()) := by
    unfold Step.evalStatement
    rw [statementKind]
    change MachineHooks.run (MachineHooks.storageLiveDyn config.lifecycle.storage localId .none)
      (Storage.withCurrent framesBefore frame machine) = _
    unfold MachineHooks.run Call.run
    rw [Storage.storage_live_dead config.lifecycle.storage framesBefore frame machine localId ty
      valid typed trivial dead noClocks]
  have step := StepFacts.step_statement (ExecutionMachine.stepHooks config limits) choice
    (Storage.withCurrent framesBefore frame machine) updated frame updatedFrame location location
    block statement (by simp [Storage.withCurrent, Stack.currentFrame?]) frameLocation blockAt
    statementAt effect (by simp [updated, Storage.withCurrent])
    (by simp [updated, Storage.withCurrent, Stack.currentFrame?])
    (by simpa [updatedFrame] using frameLocation) (by simp [updated, Storage.withCurrent])
  exact ⟨_, step, rfl⟩

theorem assign_exact [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine afterMachine : MachineHooks.MachineState K User)
    (location : Location) (block : BasicBlock) (statement : Statement)
    (place : Place) (value : Rvalue)
    (located : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (statementAt : block.statements[location.statementIndex]? = some statement)
    (kind : statement.kind = .Assign place value)
    (effect : evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) choice value place
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore afterFrame afterMachine))
    (afterLocation : afterFrame.location = .mir location) :
    ExecutionMachine.step config limits choice (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {afterFrame with location := .mir {location with statementIndex := location.statementIndex+1}}
        afterMachine,.ok true) := by
  have statementEffect : Step.evalStatement (ExecutionMachine.stepHooks config limits) choice statement
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore afterFrame afterMachine,.ok ()) := by
    unfold Step.evalStatement
    simp only [kind]
    rw [StepAssembly.assign]
    unfold MachineHooks.run Call.run
    rw [effect]
  have step := StepFacts.step_statement (ExecutionMachine.stepHooks config limits) choice
    (Storage.withCurrent framesBefore frame machine)
    (Storage.withCurrent framesBefore afterFrame afterMachine) frame afterFrame location location
    block statement (by simp [Storage.withCurrent, Stack.currentFrame?]) located blockAt statementAt
    statementEffect (by simp [Storage.withCurrent])
    (by simp [Storage.withCurrent, Stack.currentFrame?]) afterLocation (by simp [Storage.withCurrent])
  simpa [ExecutionMachine.step, Storage.withCurrent, Array.set_push] using step

#print axioms assign_exact

end DuplicatePrefix.SourceSteps
