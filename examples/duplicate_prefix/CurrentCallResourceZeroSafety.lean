import duplicate_prefix.CurrentCallResourceReleasedWrite
import duplicate_prefix.CurrentCallResourcePrefix
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.S04FinalReturnRuleAccounting
import duplicate_prefix.PushThread

namespace DuplicatePrefix.CurrentCallResourceZeroSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags:=RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked,
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

/-- Original zero-count call completion from current uniform resources. Every
entry, release, resolver, and ORIGINAL Bool store certificate is derived here.
This is a uniform-origin live specialization, not ordinary admission. -/
theorem invoke {options remaining span before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallResourceEntry.root before #[] place race)
      before tracker data owner id offset len W place)
    (ready : CurrentCallResourceBodyReadiness.Ready C)
    (stackReady : CurrentCallPush.StackReadiness before #[]) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer W.pointer.value) len 0 place := by
  obtain ⟨out,actualEntry⟩:=CurrentCallResourceEntry.invoke limits race C stackReady 0
  let prepared:=CurrentCallResourcePreparedEntry.prepared C
  have preparedReady : CurrentCallResourceBodyReadiness.Ready prepared:=⟨ready.sourceNodes,ready.pointerTags⟩
  have rawBorrow:=RootEntryFrame.raw_borrow (CurrentCallPush.preparedMachine before #[]) (.memory place)
    (CallEntryFacts.freshRoot before).2 tracker C.state.enabled
  have empty : prepared.borrowFrame={} := Option.some.inj (C.frameBorrow.symm.trans rawBorrow)
  obtain ⟨released⟩:=CurrentCallResourceEntryRelease.release out preparedReady empty
  obtain ⟨result,traceBefore,body,identity,callee,size,located,slot0,returnPlace,extra,continuation,varargs,immediate⟩:=
    CurrentCallResourcePrefix.before_zero_return out rfl
  obtain ⟨_,_,_,oldContinuation,oldDestination,oldVarargs,oldClocks,oldBorrow,_⟩:=CurrentCallResourceEntryFacts.metadata out
  let cfg:=config options (remaining+1) span
  let current : MachineHooks.BorrowState:=⟨out.boolOutput.global,tracker.retagMode⟩
  let borrowFrame:=CurrentCallResourceEntryRelease.borrowFrame out
  let beforeReturn:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span out.finalMachine)
  let accounted:=S04FinalReturnRuleAccounting.machine options remaining span result beforeReturn
  have model:=tick_model options remaining span _ (tick_model options remaining span _ (CurrentCallResourceEntryFacts.model out))
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : accounted.threads.activeThread?=some thread:=by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    change out.finalMachine.threads.activeThread?=some thread
    rw [CurrentCallResourceEntryFacts.threads_eq out]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  have beforeMemory : accounted.memory=out.finalMachine.memory:=by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have beforeTracked : accounted.borrowTracker=some current:=by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact out.finalTracked
  have frameTracked : result.extra.borrowTracker=some borrowFrame:=by rw [extra];exact oldBorrow
  have plan : StackPopRelease.Plan current.global.protectedTags borrowFrame.protectedTags.toList accounted.memory released.memory:=by
    rw [beforeMemory]
    exact released.plan
  let post : RootState:=⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
    (ActualPopPlan.released accounted released.memory current borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩
  have postUser : post.machine.user=accounted.user:=by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have postMemory : post.machine.memory=released.memory:=by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have addresses : accounted.user.addresses=out.finalMachine.user.addresses:=by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨initialWindow,initialPointer,initialId,initialOffset,initialBinding⟩:=CurrentCallResourceRootPhysical.of_entry out
  obtain ⟨window,pointerEq,idEq,offsetEq,binding⟩:=CurrentCallRootPhysicalWindow.plan current.global.protectedTags borrowFrame.protectedTags.toList
    out.finalMachine.memory released.memory released.plan out.finalMachine post.machine rfl postMemory
    (by rw [postUser];exact addresses) place initialWindow initialBinding
  have enabled : post.machine.borrowTracker=some {current with global:=current.global.endCall borrowFrame}:=by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have racePost : post.machine.dataRace=none:=by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> exact model.noDataRace
  have completed:=CurrentCallResourceReleasedWrite.completed out released post.machine
    {current with global:=current.global.endCall borrowFrame} postMemory rfl window
    ((idEq.trans initialId).trans out.physicalId.symm)
    ((offsetEq.trans initialOffset).trans out.physicalOffset.symm) (pointerEq.trans initialPointer)
  have resolved:=CurrentCallRootPhysicalWindow.resolve options remaining span post place window binding
  have extras : post.machine.user.payload.payload.user.runtime.extras=(CurrentCallPush.preparedMachine before #[]).user.payload.payload.user.runtime.extras:=by
    rw [postUser]
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rw [CurrentCallResourceEntryFacts.user_eq out]
    rfl
  have readyPost : CurrentCallBoolProtection.WindowReady post.machine window.id window.offset.toNat 1:=by
    have transferred:=prepared.ready.transport extras
    rw [idEq,initialId,offsetEq,initialOffset]
    exact transferred
  have accountedGhost : accounted.user.payload.ghost=false:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact model.ghostOff
  have accountedShallow : accounted.user.payload.validation=.Shallow:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact model.shallow
  have accountedBackend : accounted.user.payload.payload.user.backend=.none:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact model.noBackend
  have postGhost : post.machine.user.payload.ghost=false:=by rw [postUser];exact accountedGhost
  have postShallow : post.machine.user.payload.validation=.Shallow:=by rw [postUser];exact accountedShallow
  have postBackend : post.machine.user.payload.payload.user.backend=.none:=by rw [postUser];exact accountedBackend
  have valid0 : (0 : MIR.LocalId)<result.locals.size:=by rw [size];decide
  have cell0:=Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slot0)
  have destination : result.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩:=by rw [returnPlace,oldDestination];rfl
  have stop : result.returnContinuation=.stop true:=by rw [continuation,oldContinuation];rfl
  have noVarargs : result.vaList=#[]:=by rw [varargs,oldVarargs];rfl
  have noClocks : result.extra.dataRace=none:=by rw [extra];exact oldClocks.trans (CurrentCallResourceEntry.root before #[] place race).noClocks
  obtain ⟨updated,returned,_,_,_⟩:=CurrentCallRootReturn.step_of_release_copy options limits remaining span result accounted current borrowFrame
    beforeTracked frameTracked released.memory plan thread active post rfl body located valid0 noClocks accountedGhost stop immediate noVarargs
    place window binding {current with global:=current.global.endCall borrowFrame} enabled racePost postBackend postGhost postShallow readyPost completed resolved
    true C.validationFuel model.debugOff C.validationEq (by rw [cell0]) (by rw [cell0]) destination
    beforeReturn rfl model.unchecked model.noGc model.fixedScheduler
  let installed:=Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine
  let finalState:=CanonicalCopy.replaceAllocation post window.id window.entry.kind updated
  have trace : SuccessfulTrace.Trace cfg limits installed finalState:=SuccessfulTrace.append traceBefore (.next returned (.refl _))
  have terminal : ExecutionMachine.step cfg limits () finalState=(finalState,.ok false):=rfl
  have terminalEmpty : finalState.stack.frames=#[]:=rfl
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨cfg,limits,fun _ _=>True⟩
  have entry : CallSafety.IsCallEntry 1 installed:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 finalState:=by change finalState.stack.frames.size<1;rw [terminalEmpty];decide
  exact ⟨installed,finalState,actualEntry,trace,terminal,terminalEmpty,
    SuccessfulTrace.no_errors context 1 installed finalState entry trace past,
    SuccessfulTrace.no_ub context 1 installed finalState entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.CurrentCallResourceZeroSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceZeroSafety" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved original resource-zero result dependency {dependency}"
