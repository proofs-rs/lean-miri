import duplicate_prefix.Storage
import Miri.Interpreter.PlaceMachine

namespace DuplicatePrefix.LocalWrites
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

open Lean Elab Tactic in
elab "simp_local_write" : tactic => do
  let env ← getEnv
  let names ← ([".Interpreter.stackLift", ".Interpreter.placeLift"] : List String).mapM fun (suffix : String) => do
    let found := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then
        some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected one source helper {suffix}, got {found}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    placeWriteLocalImmediate, MachineHooks.currentFrame, MachineHooks.setCurrentFrame,
    MachineHooks.afterLocalWrite, Storage.withCurrent, Stack.currentFrame?,
    Frame.getLocalOperand, Frame.getLocal,
    Frame.setLocalOperand, Frame.replaceLocalValue, LocalState.access,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set, pure, Except.pure, EStateM.pure,
    Except.bind, Except.mapError, $[$names:ident],*]))

theorem immediate_write
    (validation : MachineHooks.M K User Bool)
    (debugAbiCheck : Immediate Provenance → LocalLayout → MachineHooks.M K User Unit)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (validationFalse : validation = pure false)
    (noDebug : debugAbiCheck value layout = pure ()) :
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      validation MachineHooks.afterLocalWrite debugAbiCheck localId layout value
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  simp_local_write

theorem immediate_write_observed
    (validation : MachineHooks.M K User Bool)
    (debugAbiCheck : Immediate Provenance → LocalLayout → MachineHooks.M K User Unit)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (validationFalse : validation (Storage.withCurrent framesBefore
      {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) =
      .ok false (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine))
    (noDebug : debugAbiCheck value layout = pure ()) :
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      validation MachineHooks.afterLocalWrite debugAbiCheck localId layout value
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  simp_local_write

open Lean Elab Tactic in
elab "simp_local_place" : tactic => do
  let env ← getEnv
  let names ← ([".Interpreter.stackLift", ".Interpreter.placeLift",
    ".Interpreter.requireCurrent", ".Interpreter.checkLocalIdentity"] : List String).mapM
      fun (suffix : String) => do
    let found := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected one source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    writePlaceImmediate, writePlaceImmediateNoValidate, asMplaceOrMutableLocal,
    PlaceMachine.placeHooks, MachineHooks.currentFrame,
    Storage.withCurrent, Stack.currentFrame?, Stack.frameIndex,
    Frame.getLocalOperand, Frame.getLocal, LocalState.access,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, Except.pure, EStateM.pure, Except.bind, Except.mapError,
    $[$names:ident],*]))

theorem write_whole_local [DecidableEq K]
    (access : PlaceMachine.AccessConfig K User)
    (allocation : PlaceMachine.AllocationConfig K User)
    (compiler : PlaceMachine.CompilerHooks K User Choice) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (debug : compiler.debugAssertions = false)
    (validationFalse : compiler.validationInProgress = pure false)
    (noDebug : compiler.debugAbiCheck value layout = pure ())
    (validityOff : compiler.enforceValidity choice layout = pure false) :
    writePlaceImmediate (PlaceMachine.placeHooks access allocation compiler) choice value
      ⟨.local framesBefore.size localId none frame.localsIdentity,layout⟩
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  have write := immediate_write compiler.validationInProgress compiler.debugAbiCheck
    framesBefore frame machine localId old value layout valid live sized noClocks
    validationFalse noDebug
  simp_local_place

#print axioms immediate_write
#print axioms write_whole_local

end DuplicatePrefix.LocalWrites
