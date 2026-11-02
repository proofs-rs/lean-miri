import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.CurrentCallEmptyEntryRoot
import duplicate_prefix.CurrentCallEmptyEntryFrame
import duplicate_prefix.CurrentCallEmptyEntryPopPlan
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S04FinalReturnRuleAccounting
import duplicate_prefix.PushThread

namespace DuplicatePrefix.CurrentCallEmptyZeroCountSafety
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
    let ticks := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)
    let after := S04FinalReturnRuleAccounting.machine options remaining span frame ticks
    after.memory=machine.memory ∧ after.borrowTracker=machine.borrowTracker ∧ after.threads=machine.threads ∧
      after.dataRace=machine.dataRace ∧ after.user.addresses=machine.user.addresses ∧
      after.user.payload.ghost=machine.user.payload.ghost ∧ after.user.payload.validation=machine.user.payload.validation ∧
      after.user.payload.payload.user.backend=machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧ ticks.threads=machine.threads := by
  unfold S04FinalReturnRuleAccounting.machine RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

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

private theorem source_threads {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState)
    (localId : Miri.MIR.LocalId) (valid : localId<frame.locals.size) :
    (afterArgumentsMachine effect fresh remaining span frames frame borrow localId valid).threads=before.threads := by
  cases effect <;> rfl

private theorem finish {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (facts : CurrentCallEmptyEntryRoot.Facts out 0) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 0 place := by
  let sourceMachine := CurrentCallPush.preparedMachine before #[]
  let transported := CurrentCallPush.prepared_input input #[]
  let root := CurrentCallEntry.root before #[] place input.machine.settings.noDataRace
  let prepared := firstLive root
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  let effect := out.effect
  let firstDone := out.firstDone
  let physical := out.physical
  let room := out.room
  let certificate := out.certificate
  let output := certificate.output
  let updated := out.updated
  have outputEq : certificate.output=output := rfl
  obtain ⟨frameEq,entered,destination,idEq,offsetEq,offsetNat,extra,runtime,ready,binding,origins,bytes,length,snapshot,mutation⟩ := facts
  let currentMachine := afterArgumentsMachine effect fresh remaining span #[] prepared.frame {} 1 (prepared.valid i1)
  let currentTracker := afterArgumentsTracker effect fresh
  let argsRoot := RootArgumentsTwo.result firstDone 0
  let changed := atSpan argsRoot ⟨601⟩
  let retagged := ReturnProtection.borrowedState #[] changed.frame (CurrentCallEmptyEntryRoot.sourceBorrow effect {})
    currentMachine currentTracker room physical.id physical.entry output.child.tree
  let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
  let finalFrame := installed firstDone 0 (CurrentCallEmptyEntryRoot.sourceBorrow effect {}) physical.id currentTracker.global.nextPointerTag
  have sourceModel := model_after_arguments effect fresh remaining span #[] prepared.frame {} 1 (prepared.valid i1)
    transported.machine.settings transported.machine.state.enabled
  have model := model_after_protection options remaining span #[] changed.frame (CurrentCallEmptyEntryRoot.sourceBorrow effect {})
    currentMachine currentTracker sourceModel rfl room physical.id physical.entry output.child.tree updated
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation=fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64≤DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := RootEntryFrame.raw_locals _ _ _
  obtain ⟨result,prefixTrace,body,identity,callee,size,located,slot0,returnPlace,extraFrame,continuation,varargs,immediate⟩ :=
    zero_reaches_return effect limits remaining span root firstDone raw frameEq
      (CurrentCallEmptyEntryRoot.sourceBorrow effect {}) physical.id currentTracker.global.nextPointerTag finalMachine model fuel fuelEq
  let written := (CurrentCallEmptyEntryCompleteRelease.written output (UInt64.ofNat call.returnOffset)).tree
  let released := (CurrentCallEmptyEntryCompleteRelease.released output (UInt64.ofNat call.returnOffset)).tree
  have sourceData : CurrentCallEmptyEntrySourceData.Data effect currentMachine :=
    CurrentCallEmptyEntrySourceData.of_effect transported effect #[] prepared.frame {} 1 (prepared.valid i1)
  have qRelease : effect.allocation=some physical.id → written.releaseProtector tracker.global.nextPointerTag output.global.protectedTags=⟨written,.Released⟩ := by
    simpa only [outputEq] using certificate.qRelease
  have releaseDone : (written.releaseProtector output.tag output.global.protectedTags).status=.Released := by
    change (CurrentCallEmptyEntryCompleteRelease.released output (UInt64.ofNat call.returnOffset)).status=.Released
    exact certificate.releaseCompleted
  have bRelease : written.releaseProtector output.tag output.global.protectedTags=⟨released,.Released⟩ := by
    change written.releaseProtector output.tag output.global.protectedTags=⟨(written.releaseProtector output.tag output.global.protectedTags).tree,.Released⟩
    rw [←releaseDone]
  obtain ⟨releasedMemory,plan,lastBool⟩ := CurrentCallEmptyEntryPopPlan.construct effect currentMachine sourceData output.global.protectedTags
    physical.id output.tag {physical.entry with allocation:=updated} written released qRelease bRelease
  have allocationEq : updated.setExtra written=updated := by
    have same : updated.extra=written := extra
    rw [←same]
    exact (fun (allocation : Allocation Provenance BorrowTree) => show allocation.setExtra allocation.extra=allocation from by cases allocation;rfl) updated
  have memoryEq : finalMachine.memory=StackPopRelease.commitTree currentMachine.memory physical.id {physical.entry with allocation:=updated} written := by
    unfold StackPopRelease.commitTree
    rw [allocationEq]
    exact MemoryCopyBridge.live_update_twice currentMachine.memory physical.id
      {physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree} {physical.entry with allocation:=updated}
  have rows : output.frame.protectedTags.toList=
      (effect.allocation.toList.map fun q=>(q,tracker.global.nextPointerTag))++[(physical.id,output.tag)] := by
    rw [←outputEq,certificate.frameEq,certificate.tag]
    dsimp only [certificate,effect,physical,currentTracker]
    cases allocation : out.effect.allocation <;> simp [rootSource,allocation,FrameState.addProtector]
  rw [←memoryEq,←rows] at plan
  have initialLive : finalMachine.memory.live.find? (fun row=>row.1==physical.id)=
      some (physical.id,{physical.entry with allocation:=updated.setExtra written}) := by
    rw [allocationEq]
    exact MemoryCopyBridge.live_lookup_replaced retagged.machine.memory physical.id {physical.entry with allocation:=updated}
  have initialBinding : CandidateCallBindings.WindowBinding finalMachine physical.pointer physical.id physical.offset.toNat 1 := by
    rw [idEq,offsetNat];exact binding
  have initialReady : CurrentCallBoolProtection.WindowReady currentMachine physical.id physical.offset.toNat 1 := by
    rw [idEq,offsetNat]
    exact ready.bool.transport rfl
  obtain ⟨initialWindow,initialPointer,initialId,initialOffset,initialEntry,initialBinding',_⟩ :=
    CurrentCallEmptyEntryReturnWindow.of_mutation physical written written updated (by rw [offsetEq];exact mutation)
      initialLive rfl initialBinding initialReady rfl
  let current : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  let borrowFrame := output.frame
  have trackedFinal : finalMachine.borrowTracker=some current := by
    have globalEq : output.global=(GeneralBorrowFnEntryRegistration.registered currentTracker.global (rootSource effect) physical.id room).1 := certificate.globalEq
    change finalMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩
    rw [globalEq]
    rfl
  have frameTrackedFinal : finalFrame.extra.borrowTracker=some borrowFrame := by
    change some ((CurrentCallEmptyEntryRoot.sourceBorrow effect {}).addProtector physical.id currentTracker.global.nextPointerTag)=some output.frame
    rw [←outputEq,certificate.frameEq]
    congr 2
  let beforeReturn := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span finalMachine)
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result beforeReturn
  obtain ⟨accountMemory,accountTracked,accountThreads,accountRace,addresses,accountGhost,accountValidation,accountBackend,extras,tickThreads⟩ :=
    accounting_frame options remaining span result finalMachine
  obtain ⟨oldThread,oldActive,_⟩ := stackReady
  let thread := {oldThread with topUserRelevantFrame:=some 0}
  have threadFrame : finalMachine.threads=sourceMachine.threads :=
    (show finalMachine.threads=currentMachine.threads from rfl).trans
      (source_threads effect fresh remaining span #[] prepared.frame {} 1 (prepared.valid i1))
  have active : accounted.threads.activeThread?=some thread := by
    rw [accountThreads,threadFrame]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  let post : RootState := ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
    (ActualPopPlan.released accounted releasedMemory current borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩
  have postUser : post.machine.user=accounted.user := by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have ghost : accounted.user.payload.ghost=false := accountGhost.trans model.ghostOff
  have shallow : accounted.user.payload.validation=.Shallow := accountValidation.trans model.shallow
  have backend : accounted.user.payload.payload.user.backend=.none := accountBackend.trans model.noBackend
  have postMemory : post.machine.memory=releasedMemory := by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  obtain ⟨window,pointerEq,windowId,windowOffset,finalBinding⟩ := CurrentCallRootPhysicalWindow.plan output.global.protectedTags
    output.frame.protectedTags.toList finalMachine.memory releasedMemory plan finalMachine post.machine rfl postMemory
    (by rw [postUser];exact addresses) place initialWindow initialBinding'
  have finalLive : post.machine.memory.live.find? (fun row=>row.1==physical.id)=
      some (physical.id,{physical.entry with allocation:=updated.setExtra released}) := by rw [postMemory];exact lastBool
  have entryEq : window.entry={physical.entry with allocation:=updated.setExtra released} := by
    have found:=window.live
    rw [windowId,initialId] at found
    exact (Prod.mk.inj (Option.some.inj (found.symm.trans finalLive))).2
  have enabled : post.machine.borrowTracker=some {current with global:=current.global.endCall borrowFrame} := by
    unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have race : post.machine.dataRace=none := by unfold post GenericPopFrame.afterRelevanceAt;split <;> exact model.noDataRace
  have finalReady : CurrentCallBoolProtection.WindowReady post.machine window.id window.offset.toNat 1 := by
    rw [windowId,initialId,windowOffset,initialOffset,idEq,offsetNat]
    exact ready.bool.transport (by rw [postUser];exact extras)
  have completed : (window.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra window.pointer.provenance)
      (Size.ofBytes window.offset) (Size.ofBytes 1) .Write (current.global.endCall borrowFrame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
    rw [entryEq,pointerEq,initialPointer,windowOffset,initialOffset,offsetEq]
    simpa only [outputEq,Allocation.setExtra,Allocation.mapExtra] using certificate.originalWrite
  have resolved := CurrentCallRootPhysicalWindow.resolve options remaining span post place window finalBinding
  have enabledBefore : accounted.borrowTracker=some current := accountTracked.trans trackedFinal
  have accountPlan : StackPopRelease.Plan output.global.protectedTags output.frame.protectedTags.toList accounted.memory releasedMemory := by
    rw [accountMemory];exact plan
  have frameTracked : result.extra.borrowTracker=some borrowFrame := by rw [extraFrame];exact frameTrackedFinal
  have valid0 : (0 : Miri.MIR.LocalId)<result.locals.size := by rw [size];decide
  have cell0 : result.locals[0]=⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slot0)
  have noClocks : result.extra.dataRace=none := by rw [extraFrame];exact firstDone.noClocks
  have returnStop : result.returnContinuation=.stop true :=
    continuation.trans ((installed_control firstDone 0 (CurrentCallEmptyEntryRoot.sourceBorrow effect {}) physical.id currentTracker.global.nextPointerTag).1.trans
      ((congrArg (fun frame => frame.returnContinuation) frameEq).trans
      ((copy_control effect remaining span prepared.frame {} 1 (prepared.valid i1)).1.trans
      ((first_control root).1.trans (RootEntryFrame.raw_control sourceMachine (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2).2.2.1))))
  have noVarargs : result.vaList=#[] :=
    varargs.trans ((installed_control firstDone 0 (CurrentCallEmptyEntryRoot.sourceBorrow effect {}) physical.id currentTracker.global.nextPointerTag).2.trans
      ((congrArg (fun frame => frame.vaList) frameEq).trans
      ((copy_control effect remaining span prepared.frame {} 1 (prepared.valid i1)).2.trans
      ((first_control root).2.trans (raw_varargs sourceMachine (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2)))))
  have target : result.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩ :=
    congrArg (fun value : RuntimeStackPlace Provenance => value.toRuntimePlace) (returnPlace.trans destination)
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeReturn.user).checkedArithmetic=false :=
    (RootZeroCompleteState.tick_flags options remaining span _).1.trans ((RootZeroCompleteState.tick_flags options remaining span _).1.trans model.unchecked)
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeReturn.user).gcInterval=0 :=
    (RootZeroCompleteState.tick_flags options remaining span _).2.trans ((RootZeroCompleteState.tick_flags options remaining span _).2.trans model.noGc)
  have fixed : beforeReturn.threads.fixedScheduling=true := by rw [tickThreads];exact model.fixedScheduler
  obtain ⟨returnedAllocation,returned,_,_,_⟩ := CurrentCallRootReturn.step_of_release_copy options limits remaining span result accounted current borrowFrame
    enabledBefore frameTracked releasedMemory accountPlan thread active post rfl body located valid0 noClocks ghost returnStop immediate noVarargs
    place window finalBinding {current with global:=current.global.endCall borrowFrame} enabled race
    (by rw [postUser];exact backend) (by rw [postUser];exact ghost) (by rw [postUser];exact shallow) finalReady completed resolved true fuel model.debugOff fuelEq
    (by rw [cell0]) (by rw [cell0]) target beforeReturn rfl unchecked noGc fixed
  let cfg := config options (remaining+1) span
  let installedState := Storage.withCurrent #[] finalFrame finalMachine
  let finalState := CanonicalCopy.replaceAllocation post window.id window.entry.kind returnedAllocation
  have trace : SuccessfulTrace.Trace cfg limits installedState finalState := SuccessfulTrace.append prefixTrace (.next returned (.refl _))
  have terminal : ExecutionMachine.step cfg limits () finalState=(finalState,.ok false) := rfl
  have empty : finalState.stack.frames=#[] := rfl
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _=>True⟩
  have entry : CallSafety.IsCallEntry 1 installedState := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 finalState := by change finalState.stack.frames.size<1;rw [empty];decide
  exact ⟨installedState,finalState,entered,trace,terminal,empty,SuccessfulTrace.no_errors context 1 installedState finalState entry trace past,
    SuccessfulTrace.no_ub context 1 installedState finalState entry trace past,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

/-- The original conditional empty-source, count-zero invocation completes
through its actual frame pop and original-pointer Bool store. -/
theorem invoke {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 0 place := by
  obtain ⟨out,facts⟩ := CurrentCallEmptyEntryRoot.complete input #[] stackReady memoryReady 0
  exact finish input stackReady out facts

end
end DuplicatePrefix.CurrentCallEmptyZeroCountSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyZeroCountSafety" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty zero-count dependency {dependency}"
