import Lean
import duplicate_prefix.Storage
import Miri.Interpreter.OperandMachine

/-! Actual cached immediate-local reads, with the ghost-mode getter kept as a
state observation and the absence of local race clocks represented explicitly. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DuplicatePrefix.LocalOperands
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def cachedLayoutFrame
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (localId : LocalId) (layout : LocalLayout) (valid : localId < frame.locals.size) :=
  { frame with locals := (frame.locals.set localId
    { value := frame.locals[localId].value, layout := some layout } valid) }

open Lean Elab Tactic in
elab "simp_local_operand" : tactic => do
  let env ← getEnv
  let names ← ([".OperandMachine.stack", ".OperandMachine.lift"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some name else none
      match found with
      | [name] => pure (mkIdent name)
      | _ => throwError "expected one source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [OperandMachine.localToOp,
    MachineHooks.currentFrame, MachineHooks.setCurrentFrame, MachineHooks.afterLocalRead,
    Storage.withCurrent, Storage.current_frame, Storage.set_current_frame,
    cachedLayoutFrame, Stack.currentFrame?, Frame.getLocal, Frame.getLocalOperand,
    Frame.getOrCacheLocalLayout, LocalState.access,
    LocalState.access, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set,
    pure, Except.pure, EStateM.pure, Except.mapError, Except.bind,
    $[$names:ident],*]))

theorem cached_immediate
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (immediate : Immediate Provenance) (layout : LocalLayout) (known : Option LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate immediate))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.backendRepr.isUnsized = false)
    (noClocks : frame.extra.dataRace = none)
    (validating : Bool)
    (validationGetter : hooks.compiler.validationInProgress
      (Storage.withCurrent framesBefore frame machine) =
        .ok validating (Storage.withCurrent framesBefore frame machine)) :
    OperandMachine.localToOp hooks choice localId known
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate immediate, layout⟩ (Storage.withCurrent framesBefore frame machine) := by
  cases validating <;> simp_local_operand

/-- An immediate whose layout is not cached is read through the real
`OperandMachine.localToOp` path. The compiler query supplies a concrete layout,
which the source caches before reading the immediate. With no local race clocks,
the read hook leaves the machine unchanged. The validation getter is assumed
only at the post-cache state where the interpreter actually calls it. -/
theorem uncached_immediate
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (immediate : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate immediate))
    (uncached : frame.locals[localId].layout = none)
    (sized : layout.layout.backendRepr.isUnsized = false)
    (noClocks : frame.extra.dataRace = none)
    (layoutQuery : hooks.compiler.layout choice localId
      (Storage.withCurrent framesBefore frame machine) =
        .ok layout (Storage.withCurrent framesBefore frame machine))
    (validating : Bool)
    (validationGetter : hooks.compiler.validationInProgress
      (Storage.withCurrent framesBefore (cachedLayoutFrame frame localId layout valid) machine) =
        .ok validating (Storage.withCurrent framesBefore
          (cachedLayoutFrame frame localId layout valid) machine)) :
    OperandMachine.localToOp hooks choice localId none
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate immediate, layout⟩
        (Storage.withCurrent framesBefore (cachedLayoutFrame frame localId layout valid) machine) := by
  cases validating <;> simp_local_operand

#print axioms uncached_immediate

end DuplicatePrefix.LocalOperands
