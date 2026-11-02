import Miri.Interpreter.MachineHooks

/-! Real local read/write hooks on the newly installed empty_function frame. The caller
stack, memory, tracker and all thread state remain arbitrary. The selected
no-race profile supplies the fresh frame's absence of local race clocks. -/
namespace EmptyFunction.LocalUnit
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false
variable {K U : Type}

abbrev F := Frame Provenance LocalLayout MachineHooks.FrameExtra

def current (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U) :
    MachineHooks.State K U := ⟨⟨frames.push frame⟩,machine⟩

def withUnit (frame : F) (value : Immediate Provenance) (cached : Option LocalLayout) : F :=
  {frame with locals := #[{value := .live (.immediate value), layout := cached}]}

theorem unit_operand (frame : F) (value : Immediate Provenance) (cached : Option LocalLayout) :
    (withUnit frame value cached).getLocalOperand 0 = .ok (.immediate value) := by
  simp [withUnit, Frame.getLocalOperand, Frame.getLocal, LocalState.access,
    Except.mapError, bind, Except.bind, pure, Except.pure]

theorem replace_unit (frame : F) (old value : Immediate Provenance) (cached : Option LocalLayout) :
    (withUnit frame old cached).setLocalOperand 0 (.immediate value) =
      .ok (withUnit frame value cached) := by
  unfold Frame.setLocalOperand
  rw [unit_operand]
  simp [Frame.replaceLocalValue, withUnit, bind, Except.bind, pure, Except.pure]

theorem read_no_clocks (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (id : Miri.MIR.LocalId)
    (noClocks : frame.extra.dataRace = none) :
    MachineHooks.afterLocalRead id (current frames frame machine) =
      .ok () (current frames frame machine) := by
  simp [MachineHooks.afterLocalRead, current, MachineHooks.currentFrame,
    Stack.currentFrame?, noClocks,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure]

theorem write_no_clocks (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (id : Miri.MIR.LocalId) (storageLive : Bool)
    (noClocks : frame.extra.dataRace = none) :
    MachineHooks.afterLocalWrite id storageLive (current frames frame machine) =
      .ok () (current frames frame machine) := by
  simp [MachineHooks.afterLocalWrite, current, MachineHooks.currentFrame,
    Stack.currentFrame?, noClocks,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure]

/-- Installing the sole unit return local uses the actual storage-live driver.
The pure size classifier is compiler metadata; no allocator or callback outcome
is assumed. The old local is dead, so no allocation is deallocated. -/
theorem storage_live_zero (hooks : MachineHooks.StorageHooks K U)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (ty : Miri.MIR.TyId)
    (locals : frame.locals = #[{value := .dead, layout := none}])
    (types : frame.body.locals = #[ty])
    (trivial : hooks.veryTriviallySized ty = .ok true)
    (noClocks : frame.extra.dataRace = none) :
    MachineHooks.storageLiveDyn hooks 0 .none (current frames frame machine) =
      .ok () (current frames {frame with
        locals := #[{value := .live (.immediate .uninit), layout := none}]} machine) := by
  with_unfolding_all
    simp [MachineHooks.storageLiveDyn, current, MachineHooks.currentFrame,
      MachineHooks.setCurrentFrame, Stack.currentFrame?, Frame.getLocal,
      Frame.replaceLocalValue, Except.pure, MemPlaceMeta.hasMeta, locals, types, trivial,
      MachineHooks.afterLocalWrite, noClocks,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      set, MonadStateOf.set, EStateM.set, pure, EStateM.pure]

end EmptyFunction.LocalUnit
