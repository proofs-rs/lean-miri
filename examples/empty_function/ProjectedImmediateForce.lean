import empty_function.ProjectedForce
namespace EmptyFunction.ProjectedImmediateForce
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- The initialized-immediate force-allocation arm preserves the actual old
value write's effects. The three operation equations are internal composition
edges, derived from raw resources and the scalar/pair encoding by clients. -/
theorem from_write {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine allocatedMachine writtenMachine movedMachine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base target : LocalLayout)
    (value : Immediate Provenance) (initialized : value ≠ .uninit)
    (bound : id < frame.locals.size) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.immediate value)) (cache : slot.layout = some base)
    (sized : base.layout.isSized = true) (debugOff : compiler.debugAssertions = false)
    (allocated : MPlaceTy Provenance)
    (created : PlaceMachine.allocateStack allocation base (LocalUnit.current frames frame machine) =
      .ok allocated (LocalUnit.current frames frame allocatedMachine))
    (written : (ValidityMachine.placeHooks access allocation compiler).writeMemoryNoValidate choice value allocated
      (LocalUnit.current frames frame allocatedMachine) = .ok () (LocalUnit.current frames frame writtenMachine))
    (moved : MachineHooks.afterLocalMovedToMemory id allocated compiler.localSpan
      (LocalUnit.current frames frame writtenMachine) = .ok () (LocalUnit.current frames frame movedMachine))
    (offset : Option Size) (identity : LocalsIdentity) :
    let updated : LocalUnit.F := {frame with locals := frame.locals.set id {slot with value := .live (.indirect allocated.mplace)} bound}
    forceAllocation (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id offset identity,target⟩ (LocalUnit.current frames frame machine) =
      ((do
        let memory ← match offset with
          | none => pure allocated.mplace
          | some bytes => (ValidityMachine.placeHooks access allocation compiler).memoryOffset choice allocated.mplace bytes .wrapping .none
        pure (⟨memory,target⟩ : MPlaceTy Provenance)) :
          MachineHooks.M K (ValidityMachine.UserState U) (MPlaceTy Provenance))
        (LocalUnit.current frames updated movedMachine) := by
  dsimp only
  have got := EmptyFunction.LocalImmediate.get_local frame id slot atSlot
  have old : frame.getLocalOperand id = .ok (.immediate value) := by
    simp [Frame.getLocalOperand,got,LocalState.access,live,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  have valueAt : frame.locals[id] = slot := Array.getElem?_eq_some_iff.mp atSlot |>.2
  have replace : frame.setLocalOperand id (.indirect allocated.mplace) =
      .ok {frame with locals := frame.locals.set id {slot with value := .live (.indirect allocated.mplace)} bound} := by
    simp [Frame.setLocalOperand,old,Frame.replaceLocalValue,bound,valueAt,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  have layout : placeLayoutOfLocal (ValidityMachine.placeHooks access allocation compiler) choice id
      (LocalUnit.current frames frame machine) = .ok base (LocalUnit.current frames frame machine) := by
    simp [placeLayoutOfLocal,ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,got,cache,get,getThe,MonadStateOf.get,EStateM.get,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure]
  unfold forceAllocation
  dsimp only
  rw [requireCurrent_eq,checkLocalIdentity_debugOff _ identity (by exact debugOff)]
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    Stack.frameIndex,MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,got,old,
    Array.isEmpty_push,Array.size_push,Array.back?_push,Nat.add_sub_cancel,
    beq_self_eq_true,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    Except.pure,stackLift_ok]
  simp only [LocalUnit.current] at created moved layout written
  erw [layout]
  simp only [sized,Bool.not_true,Bool.false_eq_true,↓reduceIte,bind,Bind.bind,EStateM.bind]
  erw [created]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  cases value with
  | uninit => exact False.elim (initialized rfl)
  | scalar scalar | scalarPair first second =>
    simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,bind,Bind.bind,EStateM.bind] at written
    erw [written]
    simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    erw [moved]
    simp [MachineHooks.currentFrame,MachineHooks.setCurrentFrame,LocalUnit.current,Stack.currentFrame?,replace,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      set,MonadStateOf.set,EStateM.set,Except.pure]
    rfl
end EmptyFunction.ProjectedImmediateForce
