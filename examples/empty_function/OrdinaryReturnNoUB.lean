import empty_function.ReturnSingleton
import empty_function.ScopedErrorSafety

/-! Actual cached-unit Return composition with observed error branches.
Pop/copy equations below are internal semantic obligations, not caller input. -/
namespace EmptyFunction.OrdinaryReturnNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
abbrev Machine := MachineHooks.MachineState MiriMemoryKind RootUser

/-- All changes to a failed copy are retained. A successful copy exposes its
actual caller/frame and machine; neither is replaced by the initial state. -/
def CopyOutcome (s : Static) (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (machine : Machine) : Prop :=
  (∃ error failed,
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ frame.returnPlace
      (LocalUnit.current older caller machine) = (failed,.error error) ∧
    RunLoop.reportsUB error = false) ∨
  (∃ updated copied,
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ frame.returnPlace
      (LocalUnit.current older caller machine) = (LocalUnit.current older updated copied,.ok ()))

theorem return_outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F) (before poppedMachine : Machine)
    (body : frame.body = s.loaded.body) (location : frame.location = .mir ⟨0,1⟩)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none)
    (popped : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push caller) frame before) =
      (LocalUnit.current older caller poppedMachine,.ok frame))
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) (varargs : frame.vaList = #[])
    (copy : CopyOutcome s older caller frame poppedMachine) :
    (∃ error failed,
      (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
        (LocalUnit.current (older.push caller) frame before) = (failed,.error error) ∧
      RunLoop.reportsUB error = false) ∨
    (∃ updated copied,
      (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
        (LocalUnit.current (older.push caller) frame before) =
        (ReturnContinuation.resume older updated copied target,.ok ())) := by
  have readEq := ReturnStep.read s metadata profile remaining capacity (older.push caller) frame before locals noClocks
  have block : frame.body.basicBlocks[0]? = some Program.block := by rw [body,metadata.body]; rfl
  rcases copy with ⟨error,failed,copied,nonUB⟩ | ⟨updated,copiedMachine,copied⟩
  · left
    refine ⟨error,failed,?_,nonUB⟩
    rw [ReturnStep.source]
    generalize actualControl : ReturnStep.control s = hooks at readEq popped copied ⊢
    cases hooks
    unfold ControlFlow.returnFromCurrentFrame
    simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,
      Program.no_cleanup,Bool.false_bne,Bool.false_and,Bool.not_false,Bool.false_eq_true,
      bne_self_eq_false,Id.run,bind,Bind.bind,pure,Pure.pure,↓reduceIte]
    simp only [BodyStep.current,LocalUnit.current] at readEq popped copied
    erw [readEq]
    dsimp only
    erw [popped]
    dsimp only
    erw [copied]
  · right
    refine ⟨updated,copiedMachine,?_⟩
    have cleanup := ReturnStep.cleanup s metadata remaining capacity frame
      (LocalUnit.current older updated copiedMachine) target unwind continuation locals varargs
    rw [ReturnStep.source]
    generalize actualControl : ReturnStep.control s = hooks at readEq popped copied cleanup ⊢
    cases hooks
    unfold ControlFlow.returnFromCurrentFrame
    simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,
      Program.no_cleanup,Bool.false_bne,Bool.false_and,Bool.not_false,Bool.false_eq_true,
      bne_self_eq_false,Id.run,bind,Bind.bind,pure,Pure.pure,↓reduceIte]
    simp only [BodyStep.current,LocalUnit.current] at readEq popped copied cleanup
    erw [readEq]
    dsimp only
    erw [popped]
    dsimp only
    erw [copied]
    dsimp only
    erw [cleanup]
    dsimp only
    simp only [continuation]
    exact ReturnContinuation.returnToBlock_push older updated copiedMachine target

/-- A before-terminator failure is observed with its exact partially changed
state. No Return callback executes after this failure. -/
theorem step_hook_error (s : Static) (metadata : Metadata s)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (before : Machine)
    (body : frame.body = s.loaded.body) (location : frame.location = .mir ⟨0,1⟩)
    (failed : State) (error : StepError)
    (hook : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (LocalUnit.current frames frame before) = (failed,.error error)) :
    ExecutionMachine.step s.cfg s.limits () (LocalUnit.current frames frame before) = (failed,.error error) := by
  have block : frame.body.basicBlocks[0]? = some Program.block := by rw [body,metadata.body]; rfl
  have absent : Program.block.statements[1]? = none := rfl
  unfold ExecutionMachine.step
  generalize actualHooks : ExecutionMachine.stepHooks s.cfg s.limits = hooks at hook ⊢
  cases hooks
  unfold Step.step
  simp only [LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,absent,
    Id.run,bind,Bind.bind,pure,Pure.pure] at hook ⊢
  rw [hook]

private theorem return_terminator (s : Static) (term : Terminator) (kind : term.kind = .Return) :
    (ExecutionMachine.stepHooks s.cfg s.limits).terminator () term =
      (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false := by
  funext state
  unfold ExecutionMachine.stepHooks
  simp only [ControlFlow.evalTerminator,kind]
  rfl

theorem step_return_error (s : Static) (metadata : Metadata s)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (before afterHook : Machine)
    (body : frame.body = s.loaded.body) (location : frame.location = .mir ⟨0,1⟩)
    (hook : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (LocalUnit.current frames frame before) = (LocalUnit.current frames frame afterHook,.ok ()))
    (failed : State) (error : StepError)
    (returned : (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current frames frame afterHook) = (failed,.error error)) :
    ExecutionMachine.step s.cfg s.limits () (LocalUnit.current frames frame before) = (failed,.error error) := by
  have term := return_terminator s Program.block.terminator Program.normal_return
  have block : frame.body.basicBlocks[0]? = some Program.block := by rw [body,metadata.body]; rfl
  have absent : Program.block.statements[1]? = none := rfl
  unfold ExecutionMachine.step
  generalize actualHooks : ExecutionMachine.stepHooks s.cfg s.limits = hooks at hook returned term ⊢
  cases hooks
  unfold Step.step
  simp only [LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,absent,
    Id.run,bind,Bind.bind,pure,Pure.pure] at hook returned term ⊢
  rw [hook,term,returned]
  rfl

/-- One actual ordinary Return step either exits the original depth, or
reports its exact non-UB copy error. -/
theorem step_outcome (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F) (before afterHook poppedMachine : Machine)
    (body : frame.body = s.loaded.body) (location : frame.location = .mir ⟨0,1⟩)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none)
    (hook : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (LocalUnit.current (older.push caller) frame before) =
      (LocalUnit.current (older.push caller) frame afterHook,.ok ()))
    (popped : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push caller) frame afterHook) =
      (LocalUnit.current older caller poppedMachine,.ok frame))
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) (varargs : frame.vaList = #[])
    (copy : CopyOutcome s older caller frame poppedMachine) :
    (∃ error failed, ExecutionMachine.step s.cfg s.limits ()
      (LocalUnit.current (older.push caller) frame before) = (failed,.error error) ∧ RunLoop.reportsUB error = false) ∨
    (∃ finish, ExecutionMachine.step s.cfg s.limits ()
      (LocalUnit.current (older.push caller) frame before) = (finish,.ok true) ∧
      finish.stack.frames.size < (LocalUnit.current (older.push caller) frame before).stack.frames.size) := by
  rcases return_outcome s metadata profile remaining capacity older caller frame afterHook poppedMachine
    body location locals noClocks popped target unwind continuation varargs copy with
    ⟨error,failed,actual,nonUB⟩ | ⟨updated,copied,actual⟩
  · exact Or.inl ⟨error,failed,step_return_error s metadata _ frame before afterHook body location hook failed error actual,nonUB⟩
  · exact Or.inr ⟨ReturnContinuation.resume older updated copied target,
      ReturnStep.compose s metadata _ frame before afterHook _ body location hook actual,
      by simp [ReturnContinuation.resume,LocalUnit.current]⟩

/-- The one-step phase rule keeps the existing scope boundary and every
actual error. It does not require an error-free or normally returning step. -/
theorem scoped_of_step_outcome (s : Static) (depth : Nat) (start : State)
    (outcome :
      (∃ error failed, ExecutionMachine.step s.cfg s.limits () start = (failed,.error error) ∧
        RunLoop.reportsUB error = false) ∨
      (∃ finish, ExecutionMachine.step s.cfg s.limits () start = (finish,.ok true) ∧
        finish.stack.frames.size < depth)) :
    ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) depth start := by
  apply ScopedErrorSafety.noUB_of_invariant (fun state => state = start ∨ state.stack.frames.size < depth)
  · exact Or.inl rfl
  · intro before after choice phase inside permitted actual
    cases choice
    rcases phase with equal | outside
    · subst before
      rcases outcome with ⟨error,failed,step,_⟩ | ⟨finish,step,outside⟩
      · rw [step] at actual; cases actual
      · rw [step] at actual; cases actual; exact Or.inr outside
    · omega
  · intro before after choice error phase inside permitted actual
    cases choice
    rcases phase with equal | outside
    · subst before
      rcases outcome with ⟨reported,failed,step,nonUB⟩ | ⟨finish,step,_⟩
      · rw [step] at actual; cases actual; exact nonUB
      · rw [step] at actual; cases actual
    · omega

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.OrdinaryReturnNoUB.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary Return outcome axiom {dependency} in {name}"
  logInfo m!"Audited {count} ordinary Return declarations"
end EmptyFunction.OrdinaryReturnNoUB
