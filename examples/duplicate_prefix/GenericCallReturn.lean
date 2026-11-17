import duplicate_prefix.RootOperandCopy
import duplicate_prefix.RootUsizeWrite
import Miri.Interpreter.ExecutionControl
import duplicate_prefix.StepFacts

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.GenericCallReturn
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter

/-- Exact source return ordering, including cleanup before the caller jump.
The pop stage is the source action that releases protectors before removing
its current frame. All intermediate states are retained. -/
theorem normal_goto
    (hooks : ControlHooks P L E M C Op) (choice : C)
    (s0 s1 s2 s3 s4 : StepState P L E M)
    (frame popped : Frame P L E) (location : Miri.MIR.Location) (block : Miri.MIR.BasicBlock)
    (value : Op) (target : BasicBlockId) (unwind : UnwindAction)
    (current : s0.stack.currentFrame? = some frame)
    (atLocation : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (normal : block.cleanup = false)
    (read : hooks.returnOperand choice s0 = (s1, .ok value))
    (pop : hooks.popFrame choice s1 = (s2, .ok popped))
    (copy : hooks.copyReturn choice value popped.returnPlace s2 = (s3, .ok ()))
    (cleanup : hooks.cleanupFrame choice false popped s3 = (s4, .ok .normal))
    (continuation : popped.returnContinuation = .goto (some target) unwind) :
    ControlFlow.returnFromCurrentFrame hooks choice false s0 = ControlFlow.goToBlock target s4 := by
  simp [ControlFlow.returnFromCurrentFrame, current, atLocation, blockAt, normal, read, pop,
    copy, cleanup, continuation, ControlFlow.returnToBlock]

/-- The source constructor's real EStateM stages instantiate the return driver;
no replacement dictionary or alternative pop/copy/cleanup semantics is used. -/
theorem execution_normal_goto [DecidableEq K]
    (bodySpan : Frame Provenance LocalLayout MachineHooks.FrameExtra → Except StepError SpanRef)
    (lifecycle : CallMachine.Lifecycle K U C)
    (access : PlaceMachine.AccessConfig K U)
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (copyHooks : PlaceCopyHooks Provenance (MachineHooks.State K U) C)
    (queries : TypedRetag.Hooks K U)
    (helpers : FunctionCalls.Hooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra O X F A)
    (unwindTerminate : C → UnwindTerminateReason → MachineHooks.M K U CallInstance)
    (choice : C) (s0 s1 s2 s3 s4 : MachineHooks.State K U)
    (frame popped : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (location : Miri.MIR.Location) (block : Miri.MIR.BasicBlock) (value : OpTy Provenance)
    (target : BasicBlockId) (unwind : UnwindAction)
    (current : s0.stack.currentFrame? = some frame)
    (atLocation : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (normal : block.cleanup = false)
    (read : place.localToOp choice 0 s0 = .ok value s1)
    (pop : TypedMachineBindings.popRaw (TypedMachineBindings.retagHooks access queries) s1 = .ok popped s2)
    (copy : copyRuntimePlace place copyHooks choice value popped.returnPlace.toRuntimePlace true s2 = .ok () s3)
    (cleanup : CallMachine.cleanup lifecycle choice false popped s3 = .ok .normal s4)
    (continuation : popped.returnContinuation = .goto (some target) unwind) :
    ControlFlow.returnFromCurrentFrame
      (ExecutionControl.hooks bodySpan lifecycle access place copyHooks queries helpers unwindTerminate)
      choice false s0 = ControlFlow.goToBlock target s4 := by
  apply normal_goto _ choice s0 s1 s2 s3 s4 frame popped location block value target unwind
    current atLocation blockAt normal
  · simpa [ExecutionControl.hooks, MachineHooks.run, Call.run, read]
  · simpa [ExecutionControl.hooks, MachineHooks.run, Call.run, pop]
  · simpa [ExecutionControl.hooks, MachineHooks.run, Call.run, copy]
  · simpa [ExecutionControl.hooks, MachineHooks.run, Call.run, cleanup]
  · exact continuation

/-- A successful source jump changes exactly the current caller location. -/
theorem goto_current
    (frames : Array (Frame P L E)) (caller : Frame P L E) (machine : M)
    (target : BasicBlockId) :
    ControlFlow.goToBlock target (⟨⟨frames.push caller⟩, machine⟩ : StepState P L E M) =
      (⟨⟨frames.push {caller with location := .mir ⟨target, 0⟩}⟩, machine⟩, .ok ()) := by
  simp [ControlFlow.goToBlock, ControlFlow.setLocation, Stack.currentFrame?]

/-- The source return-slot read is a real local access. A cached initialized
immediate and absent local race clocks leave the machine unchanged. -/
theorem cached_local_read
    (compiler : PlaceMachine.CompilerHooks K (ValidityMachine.UserState U) C) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (value : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (validation : compiler.validationInProgress = ValidityMachine.validationInProgress)
    (ghost : machine.user.payload.ghost = false) :
    PlaceMachine.localToOp compiler choice localId (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate value, layout⟩ (Storage.withCurrent frames frame machine) := by
  simp [PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
    MachineHooks.currentFrame, MachineHooks.afterLocalRead, Storage.withCurrent,
    Stack.currentFrame?, Frame.getLocal, Frame.getLocalOperand, LocalState.access,
    valid, live, cached, sized, noClocks, validation, ValidityMachine.validationInProgress,
    ghost, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Except.mapError, Except.bind, Except.pure]

/-- Same-type return copies take the same source path for either transmute flag. -/
theorem same_layout_transmute_flag
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (MachineHooks.State K U) C)
    (prepared : CompilerProviders.Prepared) (choice : C)
    (layout : LocalLayout) (value : Immediate Provenance) (destination : RuntimePlace Provenance)
    (same : destination.layout = layout)
    (compatible : copy.compatible = CompilerCovariance.compatible prepared false) :
    copyRuntimePlace place copy choice ⟨.immediate value, layout⟩ destination true =
      copyRuntimePlace place copy choice ⟨.immediate value, layout⟩ destination false := by
  unfold copyRuntimePlace copyRuntimePlaceNoValidate
  unfold_internal ".Interpreter.placeLift"
  simp only [same, compatible, ScalarCopyStage.same_type_copy]
  funext state
  simp [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]


private theorem forIn_skip (rows : List A) (action : A → MachineHooks.M K U Unit)
    (skip : ∀ row ∈ rows, action row = pure ()) :
    (forIn rows () (fun row _ => do action row; pure (.yield ()))) =
      (pure () : MachineHooks.M K U Unit) := by
  induction rows with
  | nil => simp [List.forIn_nil]
  | cons head tail ih =>
    have first := skip head (by simp)
    have rest := ih (fun row member => skip row (by simp [member]))
    simp only [List.forIn_cons, first, bind, EStateM.bind, pure, EStateM.pure]
    exact rest

/-- Detached cleanup has no deallocation work for dead/immediate locals and
an empty varargs list; the real normal-unwind handler returns Normal. -/
theorem cleanup_immediate_frame
    (lifecycle : CallMachine.Lifecycle K U C) (unwind : Unwind.Hooks K U C O)
    (choice : C) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (ret : Option BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto ret unwindAction)
    (locals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[]) :
    CallMachine.cleanup (CallMachine.withUnwind lifecycle unwind) choice false frame = pure .normal := by
  let action := fun (slot : LocalState Provenance LocalLayout) => do
    if let .live (.indirect place) := slot.value then lifecycle.storage.deallocateStack place.ptr
  have skip (slot : LocalState Provenance LocalLayout) (member : slot ∈ frame.locals.toList) :
      action slot = (pure () : MachineHooks.M K U Unit) := by
    have safe := locals slot (by simpa using member)
    cases value : slot.value with
    | dead => simp [action, value]
    | live op =>
      cases op with
      | immediate value => simp [action, value]
      | indirect memory => exact False.elim (safe memory value)
  have loop := forIn_skip frame.locals.toList action skip
  unfold CallMachine.cleanup
  simp only [continuation, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have bodyEq : (fun (slot : LocalState Provenance LocalLayout) (_ : Unit) => do
      action slot
      pure (.yield ())) = (fun (slot : LocalState Provenance LocalLayout) (_ : Unit) => do
      if let .live (.indirect place) := slot.value then lifecycle.storage.deallocateStack place.ptr
      pure (.yield ()) : LocalState Provenance LocalLayout → Unit → MachineHooks.M K U (ForInStep Unit)) := by
    funext slot unit
    cases value : slot.value with
    | dead => simp only [action, value]; rfl
    | live op => cases op <;> simp only [action, value] <;> rfl
  have arrayLoop : (forIn frame.locals () (fun slot _ => do
      if let .live (.indirect place) := slot.value then lifecycle.storage.deallocateStack place.ptr
      pure (.yield ()))) = (pure () : MachineHooks.M K U Unit) := by
    simpa only [Array.forIn_toList, bodyEq] using loop
  change ((do
    forIn frame.locals () (fun (slot : LocalState Provenance LocalLayout) _ => do
      if let .live (.indirect place) := slot.value then lifecycle.storage.deallocateStack place.ptr
      pure (.yield ()))
    for arg in frame.vaList do lifecycle.storage.deallocateStack arg.mplace.ptr
    let result ← (CallMachine.withUnwind lifecycle unwind).afterPop choice frame false
    if result == .noCleanup then throw (.invalidProgram "after_stack_pop returned NoCleanup during cleanup")
    pure result) : MachineHooks.M K U ReturnAction) = _
  rw [arrayLoop, varargs]
  funext state
  simp [CallMachine.withUnwind, Unwind.afterStackPop, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]


/-- Apply detached cleanup to the actual lifecycle when its after-pop field is
exactly the source unwind adapter. -/
theorem cleanup_immediate_frame_from_after_pop
    (lifecycle : CallMachine.Lifecycle K U C) (unwind : Unwind.Hooks K U C O)
    (afterPop : lifecycle.afterPop = fun c frame unwinding =>
      Unwind.afterStackPop unwind c frame.extra unwinding)
    (choice : C) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (ret : Option BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto ret unwindAction)
    (locals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[]) :
    CallMachine.cleanup lifecycle choice false frame = pure .normal := by
  have source := cleanup_immediate_frame lifecycle unwind choice frame ret unwindAction continuation locals varargs
  have same : CallMachine.withUnwind lifecycle unwind = lifecycle := by
    unfold CallMachine.withUnwind
    rw [← afterPop]
  rw [same] at source
  exact source

/-- The exact control dictionary constructed inside production stepHooks. -/
def sourceControl [DecidableEq K] (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) :=
  let config := ExecutionMachine.withValidation config limits
  let calls := ExecutionMachine.callHooks config limits
  let helpers := ExecutionCalls.helpers config.helpers calls
  ExecutionControl.hooks config.control.bodySpan config.lifecycle config.access
    (ExecutionMachine.projectionHooks config).place config.copy config.retag helpers config.unwindTerminateFunction

theorem return_terminator_source [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (terminator : Terminator) (state : MachineHooks.State K U)
    (kind : terminator.kind = .Return) :
    (ExecutionMachine.stepHooks config limits).terminator choice terminator state =
      ControlFlow.returnFromCurrentFrame (sourceControl config limits) choice false state := by
  simp only [ExecutionMachine.stepHooks, ControlFlow.evalTerminator, kind]
  rfl

/-- The actual Return statement completes one production machine step after
its source accounting and return driver transitions have been established. -/
theorem return_step_exact [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (before accounted after : MachineHooks.State K U)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (location : Miri.MIR.Location) (block : Miri.MIR.BasicBlock)
    (current : before.stack.currentFrame? = some frame)
    (located : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (noStatement : block.statements[location.statementIndex]? = none)
    (kind : block.terminator.kind = .Return)
    (accounting : (ExecutionMachine.stepHooks config limits).beforeTerminator choice before = (accounted, .ok ()))
    (returned : ControlFlow.returnFromCurrentFrame (sourceControl config limits) choice false accounted = (after, .ok ())) :
    ExecutionMachine.step config limits choice before = (after, .ok true) := by
  apply StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) choice before accounted after
    frame location block current located blockAt noStatement accounting
  rw [return_terminator_source config limits choice block.terminator accounted kind]
  exact returned


open Lean Elab Command in
run_cmd do
  for declaration in [``cleanup_immediate_frame_from_after_pop, ``return_terminator_source, ``return_step_exact, ``forIn_skip, ``cleanup_immediate_frame, ``cached_local_read, ``same_layout_transmute_flag, ``normal_goto, ``execution_normal_goto, ``goto_current] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.GenericCallReturn
