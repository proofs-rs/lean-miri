import empty_function.LocalImmediate
namespace EmptyFunction.LocalIndirectRead
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {K U C : Type}

theorem get_operand (frame : LocalUnit.F) (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : frame.locals[id]? = some slot) (place : MemPlace Provenance)
    (live : slot.value = .live (.indirect place)) : frame.getLocalOperand id = .ok (.indirect place) := by
  simp [Frame.getLocalOperand,LocalImmediate.get_local frame id slot atSlot,LocalState.access,live,
    Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem whole_cached [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (place : MemPlace Provenance) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.indirect place)) (cache : slot.layout = some layout)
    (debugOff : compiler.debugAssertions = false) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id none frame.localsIdentity,layout⟩ (LocalUnit.current frames frame machine) =
      .ok ⟨.indirect place,layout⟩ (LocalUnit.current frames frame machine) := by
  have got := LocalImmediate.get_local frame id slot atSlot
  have operand := get_operand frame id slot atSlot place live
  simp [placeToOp,placeToOpCore,ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,
    PlaceMachine.placeHooks,PlaceMachine.localToOp,PlaceMachine.localToOpCore,PlaceMachine.layoutLocal,
    MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,Stack.frameIndex,got,cache,operand,
    debugOff,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind,Except.mapError]

theorem whole_preflight [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (place : MemPlace Provenance) (bound : id < frame.locals.size)
    (atSlot : frame.locals[id]? = some slot) (live : slot.value = .live (.indirect place))
    (cache : slot.layout = none ∨ slot.layout = some layout)
    (computed : compiler.layout choice id (LocalUnit.current frames frame machine) = .ok layout (LocalUnit.current frames frame machine))
    (debugOff : compiler.debugAssertions = false) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id none frame.localsIdentity,layout⟩ (LocalUnit.current frames frame machine) =
      .ok ⟨.indirect place,layout⟩
        (LocalUnit.current frames (LocalImmediate.cached frame id slot layout bound) machine) := by
  have lay := LocalImmediate.layout_cached (ValidityMachine.compilerPolicy compiler) choice frames frame machine id slot layout bound atSlot cache computed
  have operand := get_operand (LocalImmediate.cached frame id slot layout bound) id
    {slot with layout := some layout} (LocalImmediate.cached_at frame id slot layout bound) place live
  have localRead : PlaceMachine.localToOp (ValidityMachine.compilerPolicy compiler) choice id
      (LocalUnit.current frames frame machine) =
      .ok ⟨.indirect place,layout⟩ (LocalUnit.current frames (LocalImmediate.cached frame id slot layout bound) machine) := by
    unfold PlaceMachine.localToOp PlaceMachine.localToOpCore
    simp only [bind,Bind.bind,EStateM.bind]
    rw [lay]
    simp [MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,operand,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  unfold placeToOp placeToOpCore
  simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    Stack.frameIndex,LocalUnit.current,debugOff,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind]
  simp only [LocalUnit.current,ValidityMachine.compilerPolicy,debugOff] at localRead
  rw [localRead]
end EmptyFunction.LocalIndirectRead
