import empty_function.LocalIndirectPrefix
import empty_function.MemoryInitOutcome
import empty_function.ProtectionOutcome
import empty_function.PushedProfile
import empty_function.ReleaseReadyPop
import empty_function.BodyTotal
import empty_function.OrdinaryCopyNoUB
import empty_function.ReturnGeometry
import empty_function.CallLevelNoUB
import empty_function.TerminatorStep
import empty_function.ScopedErrorSafety
namespace EmptyFunction.LocalIndirectPhasesNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
abbrev Machine := ProtectionOutcome.Machine

/-- Source-derived local pre-protection data, retaining the original packet. -/
structure Prefix (s : Static) (metadata : Metadata s) (p : Packet)
    (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (memory : MemPlace Provenance) where
  older : Array LocalUnit.F
  bound : destination.localId < destination.caller.locals.size
  frame : LocalUnit.F
  machine : Machine
  original : p.before.stack.frames = older.push destination.caller
  actual : install s p = InitializationPrefix.protectedTail s
    ⟨LocalIndirectPrefix.selectedPlace memory destination.offset,s.abi.ret.layout⟩ metadata.preamble
    (LocalUnit.current (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames
      {frame with location := .unwinding metadata.localSpan} machine)
  body : frame.body = s.loaded.body
  identity : frame.bodyIdentity = s.loaded.identity
  function : frame.functionInstance = s.functionInstance
  location : frame.location = .unwinding metadata.preamble
  locals : frame.locals = #[{value := .dead,layout := none}]
  borrowed : frame.extra.borrowTracker = some {}
  noClocks : frame.extra.dataRace = none
  returnPlace : frame.returnPlace = p.destination
  continuation : frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)
  varargs : frame.vaList = #[]
  callerArg : frame.trackCallerArg = none
  machineTracker : machine.borrowTracker = some input.tracker
  noRace : machine.dataRace = none
  noGhost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  pushed : ∃ previous, machine = FrameRelevance.pushedMachine
    (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame previous
    (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1

theorem from_current (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (memory : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect memory) : Nonempty (Prefix s metadata p input destination memory) := by
  obtain ⟨older,bound,frame,machine,original,actual,body,identity,function,location,locals,borrowed,noClocks,
    returnPlace,continuation,varargs,callerArg,machineTracker,noRace,noGhost,shallow,pushed⟩ :=
    LocalIndirectPrefix.local_prefix s metadata profile p runtime input destination memory indirect
  exact ⟨⟨older,bound,frame,machine,original,actual,body,identity,function,location,locals,borrowed,noClocks,
    returnPlace,continuation,varargs,callerArg,machineTracker,noRace,noGhost,shallow,pushed⟩⟩

private theorem ready_after_terminator (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : Machine) (borrow : FrameState) (ready : ProtectionOutcome.ReleaseReady machine borrow) :
    ProtectionOutcome.ReleaseReady (TerminatorStep.after (LocalUnit.current frames frame machine)).machine borrow := by
  cases ready with
  | empty tracker enabled borrowed => exact .empty tracker enabled borrowed
  | nondata tracker id tag info enabled borrowed metadata kind => exact .nondata tracker id tag info enabled borrowed metadata kind
  | live tracker id tag entry enabled borrowed lookup released => exact .live tracker id tag entry enabled borrowed lookup released

/-- The positive-offset source query is an internal successful-protection post.
Zero offset and whole locals do not require any geometry/query assumption. -/
def Queries (s : Static) (metadata : Metadata s) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (memory : MemPlace Provenance) : Prop :=
  ∀ (entry : Prefix s metadata p input destination memory) (borrow : FrameState) (changed : Machine),
    let frames := (LocalCachedPush.cachedState s p input.tracker destination entry.older entry.bound).stack.frames
    let initialFrame := {entry.frame with location := .unwinding metadata.localSpan}
    let protectedFrame := {initialFrame with extra := {initialFrame.extra with borrowTracker := some borrow}}
    TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag
      ⟨LocalIndirectPrefix.selectedPlace memory destination.offset,s.abi.ret.layout⟩
      (LocalUnit.current frames initialFrame entry.machine) = .ok () (LocalUnit.current frames protectedFrame changed) →
    ∀ amount, destination.offset = some amount → amount.bytes ≠ 0 →
      EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
        (LocalUnit.current frames protectedFrame changed) memory amount .inbounds .none =
        .ok (ProjectedIndirectPreflight.shifted memory amount)

/-- Actual local-none/local-some initialization/body/Return composition. The
protection and positive-query proofs are internal obligations for the producer. -/
theorem noUB (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (memory : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect memory)
    (protection : ∀ entry : Prefix s metadata p input destination memory,
      ProtectionOutcome.Outcome s ⟨LocalIndirectPrefix.selectedPlace memory destination.offset,s.abi.ret.layout⟩
        (LocalCachedPush.cachedState s p input.tracker destination entry.older entry.bound).stack.frames
        {entry.frame with location := .unwinding metadata.localSpan} entry.machine)
    (queries : Queries s metadata p input destination memory) : CallLevelNoUB.NoUB s p := by
  obtain ⟨entry⟩ := from_current s metadata profile p runtime input destination memory indirect
  let caller := LocalImmediate.cached destination.caller destination.localId destination.slot destination.baseLayout entry.bound
  let frames := entry.older.push caller
  let initialFrame := {entry.frame with location := .unwinding metadata.localSpan}
  let selected : MPlaceTy Provenance := ⟨LocalIndirectPrefix.selectedPlace memory destination.offset,s.abi.ret.layout⟩
  have outcome : ProtectionOutcome.Outcome s selected frames initialFrame entry.machine := protection entry
  have prefixEq : install s p = InitializationPrefix.protectedTail s selected metadata.preamble
      (LocalUnit.current frames initialFrame entry.machine) := entry.actual
  rcases outcome with ⟨error,failed,actual,nonUB⟩ | ⟨borrow,changed,actual,stable,releaseReady⟩
  · have protectedError : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () selected
        (LocalUnit.current frames initialFrame entry.machine) = .error error failed := actual
    have initialized := prefixEq.trans (MemoryInitOutcome.tail_error s selected metadata.preamble _ failed error protectedError)
    apply (CallLevelNoUB.noUB_iff_initialization_and_scoped s p).mpr
    constructor
    · intro reported after observed
      rw [initialized] at observed;cases observed;exact nonUB
    · intro installed observed
      rw [initialized] at observed;cases observed
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
    have protectedSuccess : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () selected
        (LocalUnit.current frames initialFrame entry.machine) = .ok () (LocalUnit.current frames protectedFrame changed) := actual
    have initialized : install s p = .ok () installed := prefixEq.trans
      (MemoryInitOutcome.tail_ok s metadata selected metadata.preamble _ frames protectedFrame changed
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
          exact (PushedProfile.fixed s metadata p.before.machine frames entry.frame previous).trans runtime.fixedScheduling
        have control : changed.user.payload.payload.user.host.control = p.before.machine.user.payload.payload.user.host.control := by
          rw [stable.control,pushed]
          exact PushedProfile.control s metadata p.before.machine frames entry.frame previous
        have gc : changed.user.payload.payload.user.host.control.gcInterval = 0 := by rw [control];exact runtime.gc
        have unchecked : changed.user.payload.payload.user.host.control.checkedArithmetic = false := by rw [control];exact runtime.unchecked
        obtain ⟨thread,active⟩ := PushedProfile.active s metadata p.before.machine frames entry.frame previous input.thread input.active
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
        have slotAt : caller.locals[destination.localId]? = some {destination.slot with layout := some destination.baseLayout} :=
          LocalImmediate.cached_at destination.caller destination.localId destination.slot destination.baseLayout entry.bound
        have callerNoClocks : caller.extra.dataRace = none := by
          change destination.caller.extra.dataRace = none
          have same := Option.some.inj (destination.current.symm.trans input.current)
          rw [same];exact input.callerNoClocks
        have returnPlace : middleFrame.returnPlace =
            .frameLocal entry.older.size destination.localId destination.offset s.abi.ret.layout caller.localsIdentity := by
          change entry.frame.returnPlace = _
          rw [entry.returnPlace,destination.encoding,entry.original]
          simp [caller,LocalImmediate.cached]
        have copy : OrdinaryReturnNoUB.CopyOutcome s entry.older caller middleFrame popped := by
          cases offset : destination.offset with
          | none =>
            have layout : destination.baseLayout = s.abi.ret.layout := by cases destination;cases offset;assumption
            have value : ({destination.slot with layout := some destination.baseLayout} : LocalState Provenance LocalLayout).value = .live (.indirect memory) := by
              rw [destination.live,indirect]
            have representation := destination.oldRepresentation memory indirect
            apply OrdinaryCopyNoUB.old_indirect_outcome s metadata profile remaining capacity validation entry.older caller
              middleFrame popped destination.localId {destination.slot with layout := some destination.baseLayout} memory
              slotAt value (by rw [layout]) representation.1 representation.2 callerNoClocks noGhostPop shallowPop
            simpa only [offset] using returnPlace
          | some amount =>
            have query : EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers
                (LocalUnit.current entry.older caller popped) memory amount .inbounds .none =
                .ok (ProjectedIndirectPreflight.shifted memory amount) := by
              by_cases zero : amount.bytes = 0
              · have same : amount = Size.ZERO := by cases amount;cases zero;rfl
                rw [same]
                simpa [ProjectedIndirectPreflight.shifted,Size.ZERO,Size.ofBytes] using
                  ProjectionZero.source s metadata (LocalUnit.current entry.older caller popped) memory
              · rw [ProjectionSnapshot.offset_congr (ConcreteProtection.source s).pointers
                  (LocalUnit.current frames protectedFrame changed) (LocalUnit.current entry.older caller popped)
                  addresses infos lives]
                exact queries entry borrow changed actual amount offset zero
            exact Or.inr ⟨caller,popped,ReturnGeometry.copy_of_query s metadata profile remaining capacity validation p
              input.tracker destination amount offset memory indirect entry.older caller middleFrame popped slotAt callerNoClocks
              noGhostPop shallowPop (by simpa only [offset] using returnPlace) query⟩
        obtain ⟨unwind,continuation⟩ : ∃ unwind, middleFrame.returnContinuation = .goto (some p.returnBlock) unwind := by
          change ∃ unwind, entry.frame.returnContinuation = .goto (some p.returnBlock) unwind
          rw [entry.continuation]
          unfold CanonicalInit.normalizedContinuation
          split <;>exact ⟨_,rfl⟩
        have varargs : middleFrame.vaList = #[] := entry.varargs
        have second := OrdinaryReturnNoUB.step_outcome s metadata profile remaining capacity entry.older caller middleFrame
          changed post popped middleBody middleLoc middleLocals middleClocks hook pop p.returnBlock unwind continuation varargs copy
        have depthEq : (LocalUnit.current frames middleFrame changed).stack.frames.size = depth p := by
          simp [LocalUnit.current,frames,depth,entry.original]
        apply ScopedErrorSafety.noUB_of_two_phases installed middle
        · intro after choice _ observed
          cases choice;rw [first] at observed;cases observed;exact Or.inl rfl
        · intro after choice _ observed
          cases choice
          rcases second with ⟨error,failed,step,nonUB⟩ | ⟨finish,step,outside⟩
          · rw [step] at observed;cases observed
          · rw [step] at observed;cases observed;rw [←depthEq];exact outside
        · intro after choice error _ observed
          cases choice;rw [first] at observed;cases observed
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
      rw [initialized] at observed;cases observed
    · intro state observed
      rw [initialized] at observed;cases observed;exact prefixSafe

/-- Whole indirect locals require no geometry contract. -/
theorem whole (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (memory : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect memory) (offset : destination.offset = none)
    (protection : ∀ entry : Prefix s metadata p input destination memory,
      ProtectionOutcome.Outcome s ⟨LocalIndirectPrefix.selectedPlace memory destination.offset,s.abi.ret.layout⟩
        (LocalCachedPush.cachedState s p input.tracker destination entry.older entry.bound).stack.frames
        {entry.frame with location := .unwinding metadata.localSpan} entry.machine) : CallLevelNoUB.NoUB s p := by
  apply noUB s metadata profile p runtime input destination memory indirect protection
  intro entry borrow changed
  dsimp only
  intro actual amount projected positive
  rw [offset] at projected
  cases projected

/-- Projected offset zero also requires no geometry contract or parent bound. -/
theorem zero (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (memory : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect memory) (offset : destination.offset = some Size.ZERO)
    (protection : ∀ entry : Prefix s metadata p input destination memory,
      ProtectionOutcome.Outcome s ⟨LocalIndirectPrefix.selectedPlace memory destination.offset,s.abi.ret.layout⟩
        (LocalCachedPush.cachedState s p input.tracker destination entry.older entry.bound).stack.frames
        {entry.frame with location := .unwinding metadata.localSpan} entry.machine) : CallLevelNoUB.NoUB s p := by
  apply noUB s metadata profile p runtime input destination memory indirect protection
  intro entry borrow changed
  dsimp only
  intro actual amount projected positive
  have same : amount = Size.ZERO := Option.some.inj (projected.symm.trans offset)
  subst amount
  exact False.elim (positive rfl)

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LocalIndirectPhasesNoUB.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved local indirect phase axiom {dependency} in {name}"
  logInfo m!"Audited {count} local indirect phase declarations"
end EmptyFunction.LocalIndirectPhasesNoUB
