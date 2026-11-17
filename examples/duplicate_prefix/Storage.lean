import Lean
import duplicate_prefix.FrameFacts
import Miri.Interpreter.MachineHooks

/-! Whole-machine local-storage operations for direct, trivially sized MIR
locals with the sequential no-local-race-clock frame representation. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DuplicatePrefix.Storage
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def withCurrent (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) : MachineHooks.State K User :=
  ⟨⟨framesBefore.push frame⟩, machine⟩

open Lean Elab Tactic in
elab "simp_storage_source" : tactic => do
  let env ← getEnv
  let names ← ([".MachineHooks.fromStack", ".MachineHooks.deallocateLocal"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some name else none
      match found with
      | [name] => pure (mkIdent name)
      | _ => throwError "expected one source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all (config := { maxSteps := 1000000 }) [MachineHooks.storageLiveDyn,
    MachineHooks.storageDead,
    MachineHooks.currentFrame, MachineHooks.setCurrentFrame, MachineHooks.afterLocalWrite,
    withCurrent, Stack.currentFrame?, Frame.getLocal, Frame.replaceLocalValue,
    MemPlaceMeta.hasMeta, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set, pure, Except.pure, EStateM.pure,
    $[$names:ident],*]))

theorem current_frame (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) :
    MachineHooks.currentFrame (withCurrent framesBefore frame machine) =
      .ok frame (withCurrent framesBefore frame machine) := by
  simp [MachineHooks.currentFrame, withCurrent, Stack.currentFrame?,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]

theorem set_current_frame
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (before after : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) :
    MachineHooks.setCurrentFrame after (withCurrent framesBefore before machine) =
      .ok () (withCurrent framesBefore after machine) := by
  simp [MachineHooks.setCurrentFrame, withCurrent, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set]

theorem storage_live_dead
    (hooks : MachineHooks.StorageHooks K User)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId) (ty : TyId)
    (valid : localId < frame.locals.size)
    (typed : frame.body.locals[localId]? = some ty)
    (trivial : hooks.veryTriviallySized ty = .ok true)
    (dead : frame.locals[localId].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    let updated := { frame with locals := (frame.locals.set localId
      { value := .live (.immediate .uninit), layout := frame.locals[localId].layout } valid) }
    MachineHooks.storageLiveDyn hooks localId .none (withCurrent framesBefore frame machine) =
      .ok () (withCurrent framesBefore updated machine) := by
  simp_storage_source

theorem storage_dead_immediate
    (hooks : MachineHooks.StorageHooks K User)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (immediate : Immediate Provenance)
    (valid : localId < frame.locals.size) (notReturn : localId ≠ 0)
    (live : frame.locals[localId].value = .live (.immediate immediate)) :
    let updated := { frame with locals := (frame.locals.set localId
      { value := .dead, layout := frame.locals[localId].layout } valid) }
    MachineHooks.storageDead hooks localId (withCurrent framesBefore frame machine) =
      .ok () (withCurrent framesBefore updated machine) := by
  simp_storage_source

end DuplicatePrefix.Storage
