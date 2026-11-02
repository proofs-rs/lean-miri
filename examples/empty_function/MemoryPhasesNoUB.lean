import empty_function.MemoryInitOutcome
import empty_function.ProtectionOutcome
import empty_function.PushedProfile
import empty_function.ReleaseReadyPop
import empty_function.BodyTotal
import empty_function.OrdinaryCopyNoUB
import empty_function.CallLevelNoUB
import empty_function.TerminatorStep

/-! Internal whole-memory-call composition. The protection outcome is supplied
by actual raw-pointer classification, never as a caller-admission field. -/
namespace EmptyFunction.MemoryPhasesNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
abbrev Machine := ProtectionOutcome.Machine

private theorem install_error (s : Static) (p : Packet) (error : StepError) (failed : State)
    (actual : install s p = .error error failed) (safe : RunLoop.reportsUB error = false) :
    CallLevelNoUB.NoUB s p := by
  apply (CallLevelNoUB.noUB_iff_initialization_and_scoped s p).mpr
  constructor
  · intro reported after outcome
    rw [actual] at outcome
    cases outcome
    exact safe
  · intro installed outcome
    rw [actual] at outcome
    cases outcome

private theorem ready_after_terminator (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : Machine) (borrow : FrameState) (ready : ProtectionOutcome.ReleaseReady machine borrow) :
    ProtectionOutcome.ReleaseReady (TerminatorStep.after (LocalUnit.current frames frame machine)).machine borrow := by
  cases ready with
  | empty tracker enabled borrowed => exact .empty tracker enabled borrowed
  | nondata tracker id tag info enabled borrowed metadata kind =>
    exact .nondata tracker id tag info enabled borrowed metadata kind
  | live tracker id tag entry enabled borrowed lookup released =>
    exact .live tracker id tag entry enabled borrowed lookup released

/-- Every actual memory-call prefix is UB-free once the internally proved
protection outcome has been supplied. No resource or supported-tape premise is
added; both initialization failures and body failures are actually observed. -/
theorem noUB (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (protection : ∀ entry : MemoryInitOutcome.Prefix s metadata p input destination,
      ProtectionOutcome.Outcome s destination.place p.before.stack.frames
        {entry.frame with location := .unwinding metadata.localSpan} entry.machine) :
    CallLevelNoUB.NoUB s p := by
  obtain ⟨entry⟩ := MemoryInitOutcome.from_current s metadata profile p runtime input destination
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp input.current
  let frames := older.push input.caller
  let initialFrame := {entry.frame with location := .unwinding metadata.localSpan}
  have outcome : ProtectionOutcome.Outcome s destination.place frames initialFrame entry.machine := by
    simpa only [frames,←original,initialFrame] using protection entry
  have prefixEq : install s p = InitializationPrefix.protectedTail s destination.place metadata.preamble
      (LocalUnit.current frames initialFrame entry.machine) := by
    simpa only [frames,←original,initialFrame] using entry.actual
  rcases outcome with ⟨error,failed,actual,nonUB⟩ | ⟨borrow,changed,actual,stable,releaseReady⟩
  · have protectedError : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination.place
        (LocalUnit.current frames initialFrame entry.machine) = .error error failed := actual
    exact install_error s p error failed
      (prefixEq.trans (MemoryInitOutcome.tail_error s destination.place metadata.preamble _ failed error protectedError)) nonUB
  · let protectedFrame : LocalUnit.F := {initialFrame with extra := {initialFrame.extra with borrowTracker := some borrow}}
    let frame := MemoryInitOutcome.readyFrame protectedFrame
    let installed := LocalUnit.current frames frame changed
    have body : frame.body = s.loaded.body := entry.body
    have identity : frame.bodyIdentity = s.loaded.identity := entry.identity
    have function : frame.functionInstance = s.functionInstance := entry.function
    have location : frame.location = .mir ⟨0,0⟩ := rfl
    have locals : frame.locals = #[{value := .live (.immediate .uninit),layout := none}] := rfl
    have noClocks : frame.extra.dataRace = none := entry.noClocks
    have frameBorrow : frame.extra.borrowTracker = some borrow := rfl
    have noGhost : changed.user.payload.ghost = false := stable.ghost.trans entry.noGhost
    have shallow : changed.user.payload.validation = .Shallow := stable.validation.trans entry.shallow
    have protectedSuccess : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination.place
        (LocalUnit.current frames initialFrame entry.machine) =
        .ok () (LocalUnit.current frames protectedFrame changed) := actual
    have initialized : install s p = .ok () installed := prefixEq.trans
      (MemoryInitOutcome.tail_ok s metadata destination.place metadata.preamble _ frames protectedFrame changed
        protectedSuccess entry.body entry.locals entry.noClocks)
    have entrySame : BodyStep.withUnit frame .uninit none = frame := by
      change {frame with locals := #[{value := .live (.immediate .uninit),layout := none}]} = frame
      rw [←locals]
    have total := BodyTotal.step s metadata profile frames frame changed identity body function location noClocks noGhost shallow
    rw [entrySame] at total
    have prefixSafe : ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed := by
      rcases total with first | ⟨reason,failed⟩
      · have firstRaw := first
        rw [←entrySame] at firstRaw
        obtain ⟨remaining,capacity,validation,successor⟩ := BodyTotal.of_success s metadata profile frames frame changed
          identity body function location noClocks noGhost shallow _ firstRaw
        let middleFrame : LocalUnit.F := {BodyStep.withUnit frame .uninit (some s.abi.ret.layout) with location := .mir ⟨0,1⟩}
        let middle := LocalUnit.current frames middleFrame changed
        have middleBody : middleFrame.body = s.loaded.body := body
        have middleLoc : middleFrame.location = .mir ⟨0,1⟩ := rfl
        have middleLocals : middleFrame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] := rfl
        have middleClocks : middleFrame.extra.dataRace = none := noClocks
        have middleBorrow : middleFrame.extra.borrowTracker = some borrow := frameBorrow
        obtain ⟨previous,pushed⟩ := entry.pushed
        have fixed : changed.threads.fixedScheduling = true := by
          rw [stable.threads,pushed]
          exact (PushedProfile.fixed s metadata p.before.machine p.before.stack.frames entry.frame previous).trans runtime.fixedScheduling
        have control : changed.user.payload.payload.user.host.control = p.before.machine.user.payload.payload.user.host.control := by
          rw [stable.control,pushed]
          exact PushedProfile.control s metadata p.before.machine p.before.stack.frames entry.frame previous
        have gc : changed.user.payload.payload.user.host.control.gcInterval = 0 := by rw [control];exact runtime.gc
        have unchecked : changed.user.payload.payload.user.host.control.checkedArithmetic = false := by rw [control];exact runtime.unchecked
        obtain ⟨thread,active⟩ := PushedProfile.active s metadata p.before.machine p.before.stack.frames entry.frame previous input.thread input.active
        have currentActive : changed.threads.activeThread? = some thread := by rw [stable.threads,pushed];exact active
        let post := (TerminatorStep.after middle).machine
        have hook : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator () middle =
            (LocalUnit.current frames middleFrame post,.ok ()) :=
          TerminatorStep.canonical s metadata (InitializationPrefix.capacity_positive s) middle fixed gc unchecked
        have readyPost : ProtectionOutcome.ReleaseReady post borrow := ready_after_terminator frames middleFrame changed borrow releaseReady
        have activePost : post.threads.activeThread? = some thread := currentActive
        obtain ⟨popped,pop,addresses,infos,lives,ghostPop,validationPop⟩ :=
          ReleaseReadyPop.pop s metadata frames middleFrame post borrow middleBorrow readyPost thread activePost
        have noGhostPop : popped.user.payload.ghost = false := ghostPop.trans noGhost
        have shallowPop : popped.user.payload.validation = .Shallow := validationPop.trans shallow
        have place : middleFrame.returnPlace = .memory destination.place := by
          change entry.frame.returnPlace = .memory destination.place
          exact entry.returnPlace.trans destination.encoding
        have copy := OrdinaryCopyNoUB.memory_outcome s metadata profile remaining capacity validation older input.caller
          middleFrame popped destination.place place destination.layout destination.sizedMetadata destination.alignmentCache noGhostPop shallowPop
        obtain ⟨unwind,continuation⟩ : ∃ unwind, middleFrame.returnContinuation = .goto (some p.returnBlock) unwind := by
          change ∃ unwind, entry.frame.returnContinuation = .goto (some p.returnBlock) unwind
          rw [entry.continuation]
          unfold CanonicalInit.normalizedContinuation
          split <;>exact ⟨_,rfl⟩
        have varargs : middleFrame.vaList = #[] := entry.varargs
        have second := OrdinaryReturnNoUB.step_outcome s metadata profile remaining capacity older input.caller middleFrame
          changed post popped middleBody middleLoc middleLocals middleClocks hook pop p.returnBlock unwind continuation varargs copy
        apply ScopedErrorSafety.noUB_of_two_phases installed middle
        · intro after choice _ actual
          cases choice
          rw [first] at actual
          cases actual
          exact Or.inl rfl
        · intro after choice _ actual
          cases choice
          rcases second with ⟨error,failed,step,nonUB⟩ | ⟨finish,step,outside⟩
          · rw [step] at actual;cases actual
          · rw [step] at actual;cases actual
            simpa only [LocalUnit.current,frames,←original,depth,Array.size_push] using outside
        · intro after choice error _ actual
          cases choice
          rw [first] at actual;cases actual
        · intro after choice error _ actual
          cases choice
          rcases second with ⟨reported,failed,step,nonUB⟩ | ⟨finish,step,outside⟩
          · rw [step] at actual;cases actual;exact nonUB
          · rw [step] at actual;cases actual
      · apply OrdinaryReturnNoUB.scoped_of_step_outcome s (depth p) installed
        exact Or.inl ⟨.resourceExhaustion reason,_,failed,rfl⟩
    apply (CallLevelNoUB.noUB_iff_initialization_and_scoped s p).mpr
    constructor
    · intro error failed outcome
      rw [initialized] at outcome;cases outcome
    · intro state outcome
      rw [initialized] at outcome;cases outcome
      exact prefixSafe

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.MemoryPhasesNoUB.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved memory phase axiom {dependency} in {name}"
  logInfo m!"Audited {count} memory phase declarations"
end EmptyFunction.MemoryPhasesNoUB
