import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.RootZeroCompletePrefix
import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.S05CurrentMutableProtectorRelease
import duplicate_prefix.S05CompletedChildReanchor
import duplicate_prefix.CurrentCallEntryRootRelease
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S04FinalReturnRuleAccounting
import duplicate_prefix.PushThread

/-! The positive-source count-zero invocation, through actual root release,
original-Bool validated store and terminal safety for every reachable prefix. -/
namespace DuplicatePrefix.CurrentCallZeroCountSafety
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallEntry
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private theorem frame_prefix {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {out : Output input #[]} (facts : Facts out 0) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (out.frame 0) (out.machine 0))
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (out.machine 0)))) ∧
      result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace = (out.frame 0).returnPlace ∧ result.extra = (out.frame 0).extra ∧
      result.returnContinuation = (out.frame 0).returnContinuation ∧ result.vaList = (out.frame 0).vaList ∧
      CopyHelperCleanup.AllImmediate result := by
  let initial := root before #[] place input.machine.settings.noDataRace
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    len ActualReferenceMetadata.reference).imm
  have raw : initial.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  have frameEq := facts.frame_installed
  change out.frame 0 = PositiveRootInstalledFrame.installed initial value 0 {} call.sourceId
    tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag at frameEq
  have size : (out.frame 0).locals.size = 25 := by
    rw [frameEq];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have cells (i : Fin 25) := PositiveRootInstalledFrame.slot initial raw value 0 {} call.sourceId
    tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag i
  simp only [←frameEq] at cells
  obtain ⟨body,identity,callee,_,_,_,clocks,_,location⟩ := PositiveRootInstalledFrame.metadata initial value 0 {}
    call.sourceId tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag
  rw [←frameEq] at body identity callee clocks location
  have immediate : CopyHelperCleanup.AllImmediate (out.frame 0) := by
    rw [frameEq];exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  have model := out.settings 0
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by
      unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  obtain ⟨result,trace,resultBody,resultIdentity,resultCallee,extra,returnPlace,continuation,varargs,_,resultSize,returnLocation,returnValue,all⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.machine.settings)
      model.debugOff fuel fuelEq (out.frame 0) (out.machine 0)
      (body.trans initial.body) (identity.trans initial.identity) (callee.trans initial.callee) location size
      (by simpa using congrArg LocalState.value (cells ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨3,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨2,by decide⟩))
      (clocks.trans initial.noClocks) immediate current enabled mode model.ghostOff model.shallow
      model.unchecked model.noGc model.fixedScheduler
  exact ⟨result,trace,resultBody.trans (body.trans initial.body),resultIdentity.trans (identity.trans initial.identity),
    resultCallee.trans (callee.trans initial.callee),resultSize,returnLocation,returnValue,returnPlace,extra,continuation,varargs,all⟩

/-- Actual entry and the count-zero body prepare the original root Return.
The final release/store obligations are proved separately, not assumed here. -/
theorem before_return {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) :
    ∃ out : Output input #[], Facts out 0 ∧ ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (out.frame 0) (out.machine 0))
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (out.machine 0)))) ∧
      result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace = (out.frame 0).returnPlace ∧ result.extra = (out.frame 0).extra ∧
      result.returnContinuation = (out.frame 0).returnContinuation ∧ result.vaList = (out.frame 0).vaList ∧
      CopyHelperCleanup.AllImmediate result := by
  obtain ⟨out,facts⟩ := CurrentCallEntry.complete input #[] stackReady memoryReady positive 0
  exact ⟨out,facts,frame_prefix facts⟩

/-- The original positive-source, zero-count invocation completes normally.
Every release, resolver and write certificate is derived inside this endpoint. -/
theorem invoke {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len 0 place := by
  obtain ⟨out,facts,result,prefixTrace,body,identity,callee,size,located,slot0,returnPlace,extra,continuation,varargs,immediate⟩ :=
    before_return input stackReady memoryReady positive
  obtain ⟨released⟩ := CurrentCallEntryRootRelease.of_entry out 0 facts positive
  let cfg := config options (remaining+1) span
  let current : MachineHooks.BorrowState := ⟨out.borrowed.output.global,tracker.retagMode⟩
  let borrowFrame := CurrentCallEntryRootRelease.Entry.borrowFrame out
  let beforeReturn := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span (out.machine 0))
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result beforeReturn
  obtain ⟨oldThread,oldActive,_⟩ := stackReady
  let thread := {oldThread with topUserRelevantFrame := some 0}
  have active : accounted.threads.activeThread? = some thread := by
    change (CurrentCallPush.preparedMachine before #[]).threads.activeThread? = some thread
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 oldThread 0 oldActive
  let post : RootState := ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
    (ActualPopPlan.released accounted released.memory current borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩
  have postUser : post.machine.user = accounted.user := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addresses : accounted.user.addresses = (out.machine 0).user.addresses := by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have extras : accounted.user.payload.payload.user.runtime.extras = (out.machine 0).user.payload.payload.user.runtime.extras := by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have ghost : accounted.user.payload.ghost = false := by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact (out.settings 0).ghostOff
  have shallow : accounted.user.payload.validation = .Shallow := by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact (out.settings 0).shallow
  have backend : accounted.user.payload.payload.user.backend = .none := by
    unfold accounted S04FinalReturnRuleAccounting.machine beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact (out.settings 0).noBackend
  have postMemory : post.machine.memory.live = (ActualPopPlan.released (out.machine 0) released.memory current borrowFrame).memory.live := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  obtain ⟨window,pointerEq,idEq,offsetEq,entryEq,binding⟩ := CurrentCallRootPhysicalWindow.view released.window released.binding
    (final := post.machine) (by rw [postUser];exact addresses) postMemory
  have enabled : post.machine.borrowTracker = some {current with global := current.global.endCall borrowFrame} := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have race : post.machine.dataRace = none := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> exact (out.settings 0).noDataRace
  have ready : CurrentCallBoolProtection.WindowReady post.machine window.id window.offset.toNat 1 := by
    have original := facts.memoryReady.bool
    have transported := original.transport (show post.machine.user.payload.payload.user.runtime.extras =
      (out.machine 0).user.payload.payload.user.runtime.extras from by rw [postUser];exact extras)
    rw [idEq,released.roleId,offsetEq,released.roleOffset]
    have normalized := (CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} out.source.base.raw positive).2.1
    rw [normalized]
    exact transported
  have completed : (window.entry.allocation.extra.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra window.pointer.provenance) (Size.ofBytes window.offset) (Size.ofBytes 1)
      .Write (current.global.endCall borrowFrame).protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [entryEq,pointerEq,offsetEq]
    exact CurrentCallRootRelease.write_original released.window.entry.allocation.extra (current.global.endCall borrowFrame)
      released.completion released.runtime released.completes released.order out.source.base.raw.returnPointer.grant released.node
      released.present released.window.pointer.provenance released.provenance released.window.offset released.bounds released.owned released.short
  have resolved := CurrentCallRootPhysicalWindow.resolve options remaining span post place window binding
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  have enabledBefore : accounted.borrowTracker = some current := CurrentCallEntryProtectionData.Facts.current_tracker facts
  have frameTracked : result.extra.borrowTracker = some borrowFrame := by
    rw [extra]
    exact CurrentCallEntryRootRelease.Entry.frame_tracked out 0 facts
  have valid0 : (0 : Miri.MIR.LocalId) < result.locals.size := by rw [size];decide
  have cell0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slot0)
  have frameControl := CurrentCallEntryRootRelease.Entry.frame_control out 0 facts
  have noClocks : result.extra.dataRace = none := by rw [extra];exact frameControl.1
  have beforeGhost : accounted.user.payload.ghost = false := ghost
  have returnStop : result.returnContinuation = .stop true := by rw [continuation];exact frameControl.2.1
  have noVarargs : result.vaList = #[] := by rw [varargs];exact frameControl.2.2
  have destination : result.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [returnPlace,facts.destination];rfl
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeReturn.user).checkedArithmetic = false := by
    exact (RootZeroCompleteState.tick_flags options remaining span _).1.trans
      ((RootZeroCompleteState.tick_flags options remaining span _).1.trans (out.settings 0).unchecked)
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeReturn.user).gcInterval = 0 := by
    exact (RootZeroCompleteState.tick_flags options remaining span _).2.trans
      ((RootZeroCompleteState.tick_flags options remaining span _).2.trans (out.settings 0).noGc)
  have fixed : beforeReturn.threads.fixedScheduling = true := (out.settings 0).fixedScheduler
  obtain ⟨updated,returned,_,_,_⟩ := CurrentCallRootReturn.step_of_release_copy options limits remaining span result accounted current borrowFrame
    enabledBefore frameTracked released.memory released.plan thread active post rfl body located valid0 noClocks beforeGhost returnStop
    immediate noVarargs place window binding {current with global := current.global.endCall borrowFrame} enabled race
    (by rw [postUser];exact backend) (by rw [postUser];exact ghost) (by rw [postUser];exact shallow)
    ready completed resolved true fuel (out.settings 0).debugOff fuelEq (by rw [cell0]) (by rw [cell0]) destination
    beforeReturn rfl unchecked noGc fixed
  let installed := Storage.withCurrent #[] (out.frame 0) (out.machine 0)
  let finalState := CanonicalCopy.replaceAllocation post window.id window.entry.kind updated
  have trace : SuccessfulTrace.Trace cfg limits installed finalState := SuccessfulTrace.append prefixTrace (.next returned (.refl _))
  have terminal : ExecutionMachine.step cfg limits () finalState = (finalState,.ok false) := rfl
  have empty : finalState.stack.frames = #[] := rfl
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 finalState := by
    change finalState.stack.frames.size < 1
    rw [empty];decide
  exact ⟨installed,finalState,facts.actual,trace,terminal,empty,
    SuccessfulTrace.no_errors context 1 installed finalState entry trace past,
    SuccessfulTrace.no_ub context 1 installed finalState entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.CurrentCallZeroCountSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallZeroCountSafety." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current zero-count dependency {dependency}"
