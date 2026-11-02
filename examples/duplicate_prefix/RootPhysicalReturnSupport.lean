import duplicate_prefix.ActualPopPlan
import duplicate_prefix.PhysicalBoolReturn
import duplicate_prefix.SourceControl
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootPhysicalReturnSupport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
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
theorem cleanup_stop_frame
    (lifecycle : CallMachine.Lifecycle K U C) (unwind : Unwind.Hooks K U C O)
    (choice : C) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (continuation : frame.returnContinuation = .stop true)
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

theorem cleanup_actual_stop
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame)
    (continuation : frame.returnContinuation = .stop true)
    (locals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[]) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).cleanupFrame
      () false frame state = (state,.ok .normal) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨unwind,afterPop⟩ := fields.lifecycleAfterPop
  have cleanup := cleanup_stop_frame config.lifecycle unwind () frame continuation locals varargs
  have same : CallMachine.withUnwind config.lifecycle unwind = config.lifecycle := by
    unfold CallMachine.withUnwind
    rw [← afterPop]
  rw [same] at cleanup
  change MachineHooks.run (CallMachine.cleanup config.lifecycle () false frame) state = _
  rw [cleanup]
  rfl

theorem normal_stop
    (hooks : ControlHooks P L E M C Op) (choice : C)
    (s0 s1 s2 s3 : StepState P L E M)
    (frame : Frame P L E) (location : MIR.Location) (block : MIR.BasicBlock) (value : Op)
    (current : s0.stack.currentFrame? = some frame)
    (located : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (normal : block.cleanup = false)
    (read : hooks.returnOperand choice s0 = (s1,.ok value))
    (pop : hooks.popFrame choice s1 = (s2,.ok frame))
    (copy : hooks.copyReturn choice value frame.returnPlace s2 = (s3,.ok ()))
    (cleanup : hooks.cleanupFrame choice false frame s3 = (s3,.ok .normal))
    (continuation : frame.returnContinuation = .stop true)
    (empty : s3.stack.frames = #[]) :
    ControlFlow.returnFromCurrentFrame hooks choice false s0 = (s3,.ok ()) := by
  simp [ControlFlow.returnFromCurrentFrame, current, located, blockAt, normal, read, pop, copy, cleanup, continuation, empty]

#print axioms cleanup_actual_stop
#print axioms normal_stop
end DuplicatePrefix.RootPhysicalReturnSupport
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootPhysicalReturnSupport.cleanup_actual_stop,
      ``DuplicatePrefix.RootPhysicalReturnSupport.normal_stop] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root physical return support dependency {dependency}"
