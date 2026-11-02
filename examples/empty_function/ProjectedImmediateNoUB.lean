import empty_function.LocalImmediateTotal
import empty_function.BodyTotal
import empty_function.ProjectedReturnTotal
import empty_function.OrdinaryReturnNoUB
import empty_function.CallLevelNoUB
import empty_function.PushedSnapshot

/-! Resource-independent call-scoped UB freedom for every projected old
immediate, including uninitialized, scalar, and scalar-pair representations. -/
namespace EmptyFunction.ProjectedImmediateNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem noUB (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (offset : Size) (projected : destination.offset = some offset) (value : Immediate Provenance)
    (old : destination.oldOperand = .immediate value) : CallLevelNoUB.NoUB s p := by
  have positive := InitializationPrefix.capacity_positive s
  obtain ⟨older,bound,entry,machine,original,installEq,body,identity,function,location,locals,frameTracked,noClocks,
    returnPlace,continuation,varargs,noGhost,shallow,⟨previous,pushed⟩,tracked⟩ :=
    LocalImmediateTotal.init_projected s metadata profile p runtime input destination offset projected value old
  let caller := ProjectedModel.caller s p input.tracker destination bound
  let frames := older.push caller
  let installed := LocalUnit.current frames entry machine
  have entrySame : BodyStep.withUnit entry .uninit none = entry := by
    change {entry with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entry
    rw [←locals]
  have total := BodyTotal.step s metadata profile frames entry machine identity body function location noClocks noGhost shallow
  rw [entrySame] at total
  have prefixSafe : ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed := by
    rcases total with first | ⟨reason,failed⟩
    · have firstRaw := first
      rw [←entrySame] at firstRaw
      obtain ⟨remaining,capacity,validation,successor⟩ := BodyTotal.of_success s metadata profile frames entry machine
        identity body function location noClocks noGhost shallow _ firstRaw
      let frame : LocalUnit.F := {BodyStep.withUnit entry .uninit (some s.abi.ret.layout) with location := .mir ⟨0,1⟩}
      have machineEq : machine = ProjectedModel.initializedMachine s p input.tracker destination older bound frame previous := by
        rw [pushed];rfl
      let initial := ProjectedModel.initializedMachine s p input.tracker destination older bound frame previous
      let post := (TerminatorStep.after (LocalUnit.current frames frame initial)).machine
      have hook : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
          (LocalUnit.current frames frame initial) = (LocalUnit.current frames frame post,.ok ()) :=
        ProjectedReady.before_terminator s metadata positive p runtime input.tracker destination older bound frame previous
      obtain ⟨thread,active⟩ := ProjectedReady.active s metadata positive p input.tracker destination older bound frame previous input.thread input.active
      let index := thread.topUserRelevantFrame.getD frames.size
      let popped := ProjectedReady.popped s p input.tracker destination older bound frame previous index
      have raw := ProjectedReady.resources s metadata positive p runtime input destination older bound frame previous index
      have enabled : post.borrowTracker = some input.tracker := by
        have same : popped.borrowTracker = post.borrowTracker := by
          unfold popped ProjectedReady.popped FrameExit.afterRelevanceAt
          split <;>rfl
        exact same.symm.trans raw.2.2.1
      have bodyFrame : frame.body = s.loaded.body := body
      have locFrame : frame.location = .mir ⟨0,1⟩ := rfl
      have localsFrame : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] := rfl
      have clocksFrame : frame.extra.dataRace = none := noClocks
      have trackedFrame : frame.extra.borrowTracker = some {} := frameTracked
      have pop := ReturnStep.pop s frames frame post input.tracker enabled trackedFrame thread active
      change (ReturnStep.control s).popFrame () (LocalUnit.current frames frame post) =
        (LocalUnit.current older caller popped,.ok frame) at pop
      have destinationEq : p.destination =
          .frameLocal older.size destination.localId (some offset) s.abi.ret.layout destination.caller.localsIdentity := by
        rw [destination.encoding,original,projected]
        simp [Array.size_push]
      have frameReturn : frame.returnPlace =
          .frameLocal older.size destination.localId (some offset) s.abi.ret.layout destination.caller.localsIdentity :=
        returnPlace.trans destinationEq
      have copy : OrdinaryReturnNoUB.CopyOutcome s older caller frame popped := by
        unfold OrdinaryReturnNoUB.CopyOutcome
        rw [frameReturn]
        exact ProjectedReturnTotal.copy s metadata profile remaining capacity validation p runtime input destination
          offset projected value old older bound frame previous index
      obtain ⟨unwind,contFrame⟩ : ∃ unwind, frame.returnContinuation = .goto (some p.returnBlock) unwind := by
        change ∃ unwind, entry.returnContinuation = .goto (some p.returnBlock) unwind
        rw [continuation]
        unfold CanonicalInit.normalizedContinuation
        split <;>exact ⟨_,rfl⟩
      have varsFrame : frame.vaList = #[] := varargs
      have second := OrdinaryReturnNoUB.step_outcome s metadata profile remaining capacity older caller frame
        initial post popped bodyFrame locFrame localsFrame clocksFrame hook pop p.returnBlock unwind contFrame varsFrame copy
      have firstModel : ExecutionMachine.step s.cfg s.limits () installed =
          (LocalUnit.current frames frame initial,.ok true) := by
        simpa only [installed,frame,initial,←machineEq] using first
      have depthEq : (LocalUnit.current frames frame initial).stack.frames.size = depth p := by
        simp [LocalUnit.current,frames,depth,original]
      apply ScopedErrorSafety.noUB_of_two_phases installed (LocalUnit.current frames frame initial)
      · intro after choice _ observed
        cases choice;rw [firstModel] at observed;cases observed;exact Or.inl rfl
      · intro after choice _ observed
        cases choice
        rcases second with ⟨error,failed,step,nonUB⟩ | ⟨finish,step,outside⟩
        · rw [step] at observed;cases observed
        · rw [step] at observed;cases observed;rw [←depthEq];exact outside
      · intro after choice error _ observed
        cases choice;rw [firstModel] at observed;cases observed
      · intro after choice error _ observed
        cases choice
        rcases second with ⟨reported,failed,step,nonUB⟩ | ⟨finish,step,outside⟩
        · rw [step] at observed;cases observed;exact nonUB
        · rw [step] at observed;cases observed
    · apply OrdinaryReturnNoUB.scoped_of_step_outcome s (depth p) installed
      exact Or.inl ⟨.resourceExhaustion reason,_,failed,rfl⟩
  apply (CallLevelNoUB.noUB_iff_initialization_and_scoped s p).mpr
  constructor
  · intro error failed observed
    rw [installEq] at observed;cases observed
  · intro state observed
    rw [installEq] at observed;cases observed;exact prefixSafe

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ProjectedImmediateNoUB.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved projected immediate NoUB axiom {dependency} in {name}"
  logInfo m!"Audited {count} projected immediate NoUB declarations"
#print axioms noUB
end EmptyFunction.ProjectedImmediateNoUB
