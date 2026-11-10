import empty_function.LocalImmediate
import empty_function.Specification
import empty_function.ProjectedSpan
namespace EmptyFunction.ProjectedForce
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {K U C : Type} [DecidableEq K]

/-- The actual existing-indirect arm never allocates or writes the enclosing
local. Its offset operation remains the production checked pointer operation. -/
 theorem indirect (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (offset : Option Size) (layout : LocalLayout)
    (identity : LocalsIdentity) (memory : MemPlace Provenance)
    (operand : frame.getLocalOperand id = .ok (.indirect memory))
    (debugOff : compiler.debugAssertions = false) :
    forceAllocation (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id offset identity,layout⟩ (LocalUnit.current frames frame machine) =
      ((do
        let memory ← match offset with
          | none => pure memory
          | some bytes => (ValidityMachine.placeHooks access allocation compiler).memoryOffset choice memory bytes .wrapping .none
        pure (⟨memory,layout⟩ : MPlaceTy Provenance)) : MachineHooks.M K (ValidityMachine.UserState U) (MPlaceTy Provenance))
        (LocalUnit.current frames frame machine) := by
  unfold forceAllocation
  dsimp only
  rw [requireCurrent_eq,checkLocalIdentity_debugOff _ identity (by exact debugOff)]
  with_unfolding_all
    simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      LocalUnit.current,MachineHooks.currentFrame,Stack.currentFrame?,Stack.frameIndex,operand,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
      Except.pure,Except.bind,Except.mapError]
  rfl

/-- The allocator/choice domain is selected from the original caller slot,
without asking any future materialization operation to succeed. -/
 theorem needed (s : EmptyFunction.WholeCall.Static) (p : EmptyFunction.WholeCall.Packet) (tracker : MachineHooks.BorrowState)
    (destination : EmptyFunction.InputDraft.LocalDestination s p tracker) (offset : Size)
    (projected : destination.offset = some offset) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) : EmptyFunction.InputDraft.NeedsEnclosingAllocation p := by
  refine ⟨destination.caller,p.before.stack.frames.size-1,destination.localId,offset,s.abi.ret.layout,
    destination.caller.localsIdentity,destination.slot,value,destination.current,?_,destination.slotAt,?_⟩
  · simpa only [projected] using destination.encoding
  · rw [destination.live,immediate]

 theorem after_move (s : EmptyFunction.WholeCall.Static) (metadata : EmptyFunction.Specification.Metadata s)
    (capacity : 0 < s.capacity) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind EmptyFunction.Configuration.RootUser)
    (id : MIR.LocalId) (ty : TyId)
    (normalized : Input.CompilerFrameContext.localType s.prepared.compiler frame id = .ok ty)
    (place : MPlaceTy Provenance) (allocation : AllocId) (tag : BorTag)
    (provenance : place.mplace.ptr.provenance = some (.concrete allocation tag))
    (live : machine.memory.live.any (fun row => row.1 == allocation) = true)
    (noClocks : frame.extra.dataRace = none) :
    ∃ span, MachineHooks.afterLocalMovedToMemory id place s.cfg.compiler.localSpan
      (LocalUnit.current frames frame machine) =
      .ok () (LocalUnit.current frames frame {machine with allocationSpans :=
        (machine.allocationSpans.filter (fun row => row.1 != allocation)).push (allocation,span,none)}) := by
  obtain ⟨span,spanEq⟩ := EmptyFunction.ProjectedSpan.local_span s metadata capacity frames frame machine id ty normalized
  simp only [LocalUnit.current] at spanEq
  have present : ∃ (index : Nat) (valid : index < machine.memory.live.size),
      (machine.memory.live[index]'valid).1 = allocation := by
    simpa only [Array.any_eq_true,beq_iff_eq] using live
  refine ⟨span,?_⟩
  unfold MachineHooks.afterLocalMovedToMemory
  simp [provenance,MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,noClocks,
    spanEq,live,present,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]

/-- Internal composition of the uninitialized immediate arm. The actual
allocation and declaration-span hook equations are discharged independently;
the source preserves their machine effects when replacing the caller slot. -/
 theorem uninit (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine allocatedMachine movedMachine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base target : LocalLayout)
    (bound : id < frame.locals.size) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.immediate .uninit)) (cache : slot.layout = some base)
    (sized : base.layout.isSized = true) (debugOff : compiler.debugAssertions = false)
    (allocated : MPlaceTy Provenance)
    (created : PlaceMachine.allocateStack allocation base (LocalUnit.current frames frame machine) =
      .ok allocated (LocalUnit.current frames frame allocatedMachine))
    (moved : MachineHooks.afterLocalMovedToMemory id allocated compiler.localSpan
      (LocalUnit.current frames frame allocatedMachine) = .ok () (LocalUnit.current frames frame movedMachine))
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
  have old := EmptyFunction.LocalImmediate.get_operand frame id slot atSlot live
  have value : frame.locals[id] = slot := Array.getElem?_eq_some_iff.mp atSlot |>.2
  have replace : frame.setLocalOperand id (.indirect allocated.mplace) =
      .ok {frame with locals := frame.locals.set id {slot with value := .live (.indirect allocated.mplace)} bound} := by
    simp [Frame.setLocalOperand,old,Frame.replaceLocalValue,bound,value,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
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
  simp only [LocalUnit.current] at created moved layout
  erw [layout]
  simp only [sized,Bool.not_true,Bool.false_eq_true,↓reduceIte,bind,Bind.bind,EStateM.bind]
  erw [created]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  erw [moved]
  simp [MachineHooks.currentFrame,MachineHooks.setCurrentFrame,LocalUnit.current,Stack.currentFrame?,replace,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set,Except.pure]
  rfl

end EmptyFunction.ProjectedForce
