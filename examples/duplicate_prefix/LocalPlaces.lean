import duplicate_prefix.Storage
import Miri.Interpreter.PlaceDynamic

/-! Actual cached whole-local place evaluation with an empty projection. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DuplicatePrefix.LocalPlaces
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def cachePlaceLayout (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (localId : LocalId) (layout : LocalLayout) (valid : localId < frame.locals.size) :=
  { frame with locals := (frame.locals.set localId
      { value := frame.locals[localId].value, layout := some layout } valid) }

open Lean Elab Tactic in
elab "simp_local_place_source" : tactic => do
  let env ← getEnv
  let names ← ([".Interpreter.stackLift", ".Interpreter.placeLift"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected unique Place helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [localToPlace, placeLayoutOfLocal,
    cachePlaceLayout, Stack.currentFrame?, Frame.getLocal,
    Frame.getOrCacheLocalLayout, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Except.bind, Except.pure, Except.mapError, $[$names:ident],*]))

def localRuntimePlace (frameIndex : Nat) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (localId : LocalId) (layout : LocalLayout) : RuntimePlace Provenance :=
  ⟨.local frameIndex localId none frame.localsIdentity, layout⟩

theorem localToPlace_cached
    (hooks : PlaceHooks Provenance (MachineHooks.State K User) Choice MachineHooks.FrameExtra)
    (choice : Choice) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (localId : LocalId) (frameIndex : Nat)
    (layout : LocalLayout) (state : MachineHooks.State K User)
    (valid : localId < frame.locals.size)
    (getFrame : hooks.getFrame state = .ok frame state)
    (index : hooks.frameIndex state = .ok frameIndex state)
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) :
    localToPlace hooks choice localId state =
      .ok (localRuntimePlace frameIndex frame localId layout) state := by
  unfold localRuntimePlace localToPlace placeLayoutOfLocal
  simp_local_place_source
  all_goals simp [localRuntimePlace, cachePlaceLayout]

/-- The uncached source path resolves the real compiler layout, writes it into
the current frame, and returns the same local place over that updated frame. -/
theorem localToPlace_uncached
    (hooks : PlaceHooks Provenance (MachineHooks.State K User) Choice MachineHooks.FrameExtra)
    (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (frameIndex : Nat) (layout : LocalLayout) (valid : localId < frame.locals.size)
    (uncached : frame.locals[localId].layout = none)
    (sized : layout.layout.isSized = true)
    (resolve : hooks.resolveLayout choice localId
      (Storage.withCurrent framesBefore frame machine) =
      .ok layout (Storage.withCurrent framesBefore frame machine))
    (getFrame : hooks.getFrame (Storage.withCurrent framesBefore frame machine) =
      .ok frame (Storage.withCurrent framesBefore frame machine))
    (indexBefore : hooks.frameIndex (Storage.withCurrent framesBefore frame machine) =
      .ok frameIndex (Storage.withCurrent framesBefore frame machine))
    (setCached : hooks.setFrame (cachePlaceLayout frame localId layout valid)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine))
    (getCached : hooks.getFrame
      (Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine) =
      .ok (cachePlaceLayout frame localId layout valid)
        (Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine))
    (indexCached : hooks.frameIndex
      (Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine) =
      .ok frameIndex (Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine)) :
    localToPlace hooks choice localId (Storage.withCurrent framesBefore frame machine) =
      .ok (localRuntimePlace frameIndex (cachePlaceLayout frame localId layout valid) localId layout)
        (Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine) := by
  simp_local_place_source
  all_goals simp [localRuntimePlace, cachePlaceLayout]

theorem evalPlace_local_empty
    [PointerProvenance Provenance]
    (hooks : PlaceProjectionHooks Provenance (MachineHooks.State K User) Choice MachineHooks.FrameExtra)
    (choice : Choice) (localId : LocalId)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameIndex : Nat) (layout : LocalLayout) (state : MachineHooks.State K User)
    (localPlace : localToPlace hooks.place choice localId state =
      .ok (localRuntimePlace frameIndex frame localId layout) state)
    (check : hooks.place.checkPlaceType choice ⟨localId, #[]⟩
      (localRuntimePlace frameIndex frame localId layout) state = .ok () state) :
    PlaceDynamic.evalPlace hooks choice ⟨localId, #[]⟩ true state =
      .ok (localRuntimePlace frameIndex frame localId layout) state := by
  simp [PlaceDynamic.evalPlace, localPlace, check, bind, EStateM.bind, pure, EStateM.pure]

/-- Empty-projection evaluation after the actual uncached local-place path.
The place type check observes the cached-frame state produced by `localToPlace`. -/
theorem evalPlace_local_empty_uncached
    [PointerProvenance Provenance]
    (hooks : PlaceProjectionHooks Provenance (MachineHooks.State K User) Choice MachineHooks.FrameExtra)
    (choice : Choice) (localId : LocalId)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (frameIndex : Nat) (layout : LocalLayout) (valid : localId < frame.locals.size)
    (state := Storage.withCurrent framesBefore frame machine)
    (updated := Storage.withCurrent framesBefore (cachePlaceLayout frame localId layout valid) machine)
    (localPlace : localToPlace hooks.place choice localId state =
      .ok (localRuntimePlace frameIndex (cachePlaceLayout frame localId layout valid) localId layout) updated)
    (check : hooks.place.checkPlaceType choice ⟨localId, #[]⟩
      (localRuntimePlace frameIndex (cachePlaceLayout frame localId layout valid) localId layout) updated =
      .ok () updated) :
    PlaceDynamic.evalPlace hooks choice ⟨localId, #[]⟩ true state =
      .ok (localRuntimePlace frameIndex (cachePlaceLayout frame localId layout valid) localId layout) updated := by
  simp [PlaceDynamic.evalPlace, localPlace, check, bind, EStateM.bind, pure, EStateM.pure]

#print axioms localToPlace_cached
#print axioms localToPlace_uncached
#print axioms evalPlace_local_empty
#print axioms evalPlace_local_empty_uncached

end DuplicatePrefix.LocalPlaces
