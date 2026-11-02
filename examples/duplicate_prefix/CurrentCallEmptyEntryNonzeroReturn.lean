import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatch
import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.CurrentCallRootPhysicalWindow
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S04FinalReturnRuleAccounting

namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroReturn
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallEmptyTypedEntry CurrentCallEmptyEntryBool CurrentCallEmptyEntryFrame
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances false

private theorem accounting_frame (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (frame : CompilerFrameContext.ActualFrame) (machine : Before) :
    let after := S04FinalReturnRuleAccounting.machine options remaining span frame machine
    after.memory=machine.memory ∧ after.borrowTracker=machine.borrowTracker ∧ after.threads=machine.threads ∧
      after.dataRace=machine.dataRace ∧ after.user.payload.ghost=machine.user.payload.ghost ∧
      after.user.payload.validation=machine.user.payload.validation ∧
      after.user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
  unfold S04FinalReturnRuleAccounting.machine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem copy_control {options before tracker argument}
    (effect : Effect options before tracker argument) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState) (localId : Miri.MIR.LocalId) (valid : localId<frame.locals.size) :
    (resultFrame effect remaining span frame borrow localId valid).returnContinuation=frame.returnContinuation ∧
      (resultFrame effect remaining span frame borrow localId valid).vaList=frame.vaList := by
  cases effect <;> exact ⟨rfl,rfl⟩

private theorem installed_control (firstDone : RootFrame) (count : UInt64) (borrow : FrameState) (id : AllocId) (tag : BorTag) :
    (installed firstDone count borrow id tag).returnContinuation=firstDone.frame.returnContinuation ∧
    (installed firstDone count borrow id tag).vaList=firstDone.frame.vaList := by
  simp only [installed,CallEntryFacts.doneRootFrame,CallEntryFacts.liveSlot,registeredFrame,TypedRetagEntry.frameWithBorrow,
    RootArgumentsTwo.result,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame]
  repeat' constructor

private theorem first_control (root : RootFrame) :
    (firstLive root).frame.returnContinuation=root.frame.returnContinuation ∧ (firstLive root).frame.vaList=root.frame.vaList := by
  simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame]
  repeat' constructor

private theorem raw_varargs (machine : Before) (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    (CallEntryFacts.rawRootFrame machine destination identity).vaList=#[] := rfl

/-- The actual terminal tail; all release and store certificates are derived internally by its consumer. -/
theorem of_plan {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before)
    (body : CurrentCallEmptyEntryNonzeroDispatch.BodyResult out count result post)
    (current : MachineHooks.BorrowState) (tracked : post.borrowTracker=some current)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan current.global.protectedTags out.certificate.output.frame.protectedTags.toList post.memory releasedMemory)
    (thread : Miri.Concurrency.ThreadRecord) (active : post.threads.activeThread?=some thread)
    (state : RootState)
    (stateEq : state=⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
      (ActualPopPlan.released (S04FinalReturnRuleAccounting.machine options remaining span result post)
        releasedMemory current out.certificate.output.frame) (thread.topUserRelevantFrame.getD 0)⟩)
    (window : CurrentCallBoolScalarWrite.Window state.machine place)
    (binding : CandidateCallBindings.WindowBinding state.machine window.pointer window.id window.offset.toNat 1)
    (ready : CurrentCallBoolProtection.WindowReady state.machine window.id window.offset.toNat 1)
    (completed : (window.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra window.pointer.provenance)
      (Size.ofBytes window.offset) (Size.ofBytes 1) .Write
      (current.global.endCall out.certificate.output.frame).protectedTags .VisitChildrenOfAccessed).status=.Completed) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result post
  obtain ⟨memoryEq,trackedEq,threadsEq,raceEq,ghostEq,validationEq,backendEq⟩ := accounting_frame options remaining span result post
  have postUser : state.machine.user=accounted.user := by rw [stateEq];unfold GenericPopFrame.afterRelevanceAt;split <;> rfl
  have enabled : state.machine.borrowTracker=some {current with global:=current.global.endCall out.certificate.output.frame} := by
    rw [stateEq];unfold GenericPopFrame.afterRelevanceAt;split <;> rfl
  have race : state.machine.dataRace=none := by
    rw [stateEq];unfold GenericPopFrame.afterRelevanceAt;split <;> exact raceEq.trans body.model.noDataRace
  have beforeGhost : accounted.user.payload.ghost=false := ghostEq.trans body.model.ghostOff
  have canonical : rootSource out.effect=CurrentCallEmptyEntryRoot.sourceBorrow out.effect {} := by cases out.effect <;> rfl
  have frameTracked : result.extra.borrowTracker=some out.certificate.output.frame := by
    rw [body.extra]
    change some ((CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}).addProtector out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag)=some out.certificate.output.frame
    rw [out.certificate.frameEq,canonical]
    rfl
  have noClocks : result.extra.dataRace=none := by rw [body.extra];exact out.firstDone.noClocks
  have frameEq := CurrentCallEmptyEntryNonzeroDispatchState.copied out count facts
  let root := CurrentCallEmptyEntryNonzeroDispatchState.root input
  let prepared := firstLive root
  have returnStop : result.returnContinuation=.stop true :=
    body.continuation.trans ((installed_control out.firstDone count (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag).1.trans
      ((congrArg (fun frame => frame.returnContinuation) frameEq).trans
      ((copy_control out.effect remaining span prepared.frame {} 1 (prepared.valid i1)).1.trans
      ((first_control root).1.trans (RootEntryFrame.raw_control (CurrentCallPush.preparedMachine before #[])
        (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2).2.2.1))))
  have noVarargs : result.vaList=#[] :=
    body.varargs.trans ((installed_control out.firstDone count (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag).2.trans
      ((congrArg (fun frame => frame.vaList) frameEq).trans
      ((copy_control out.effect remaining span prepared.frame {} 1 (prepared.valid i1)).2.trans
      ((first_control root).2.trans (raw_varargs (CurrentCallPush.preparedMachine before #[])
        (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2)))))
  have valid0 : (0 : Miri.MIR.LocalId)<result.locals.size := by rw [body.size];decide
  have cell0 : result.locals[0]=⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans body.value)
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation=fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64≤DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  have accountPlan : StackPopRelease.Plan current.global.protectedTags out.certificate.output.frame.protectedTags.toList accounted.memory releasedMemory := by
    rw [memoryEq];exact plan
  have resolved := CurrentCallRootPhysicalWindow.resolve options remaining span state place window binding
  obtain ⟨updated,returned,_,_,_⟩ := CurrentCallRootReturn.step_of_release_copy options limits remaining span result accounted current out.certificate.output.frame
    (trackedEq.trans tracked) frameTracked releasedMemory accountPlan thread ((congrArg (fun threads => threads.activeThread?) threadsEq).trans active) state stateEq
    body.body body.location valid0 noClocks beforeGhost returnStop body.immediate noVarargs
    place window binding {current with global:=current.global.endCall out.certificate.output.frame} enabled race
    (by rw [postUser];exact backendEq.trans body.model.noBackend) (by rw [postUser];exact beforeGhost)
    (by rw [postUser];exact validationEq.trans body.model.shallow) ready completed resolved false fuel body.model.debugOff fuelEq
    (by rw [cell0]) (by rw [cell0]) (congrArg (fun value : RuntimeStackPlace Provenance => value.toRuntimePlace) body.destination)
    post rfl body.model.unchecked body.model.noGc body.model.fixedScheduler
  let cfg := config options (remaining+1) span
  let initial := Storage.withCurrent #[] (CurrentCallEmptyEntryNonzeroDispatchState.frame out count) (CurrentCallEmptyEntryNonzeroDispatchState.machine out count)
  let final := CanonicalCopy.replaceAllocation state window.id window.entry.kind updated
  have trace : SuccessfulTrace.Trace cfg limits initial final := SuccessfulTrace.append body.trace (.next returned (.refl _))
  have empty : final.stack.frames=#[] := by
    change state.stack.frames=#[]
    exact congrArg (fun value : RootState => value.stack.frames) stateEq
  have terminal : ExecutionMachine.step cfg limits () final=(final,.ok false) := by
    simp only [ExecutionMachine.step,Step.step,Stack.currentFrame?,empty]
    rfl
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _=>True⟩
  have entry : CallSafety.IsCallEntry 1 initial := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final := by change final.stack.frames.size<1;rw [empty];decide
  exact ⟨initial,final,CurrentCallEmptyEntryNonzeroDispatchState.actual out count facts,trace,terminal,empty,
    SuccessfulTrace.no_errors context 1 initial final entry trace past,SuccessfulTrace.no_ub context 1 initial final entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroReturn" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved nonzero return dependency {dependency}"
