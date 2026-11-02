import duplicate_prefix.CurrentCallResourceCurrentRelease
import duplicate_prefix.CurrentCallResourceReleaseWrite
import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.S04FinalReturnRuleAccounting
namespace DuplicatePrefix.CurrentCallResourceRootFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- The common actual root Return consumes the original pointer and current
released-parent resources; no initial live destination window is needed. -/
theorem finish_pointer {returnId returnOffset machine tracker bData bOwner}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (place : MPlaceTy Provenance)
    (original : PointerInstance) (originalId : original.allocation=returnId)
    (B : UniformWindow machine tracker bData bOwner returnId returnOffset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (sameId : physical.id=returnId) (sameOffset : physical.offset.toNat=returnOffset)
    (samePointer : physical.pointer=original.value)
    (parentIssued : SpatialDelegation machine tracker returnId B.allocation B.precise.completion original.grant)
    (parentBinding : PointerBinds B.allocation original)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (released : CurrentCallResourceCurrentRelease.Released B borrowFrame original.grant physical.offset physical.entry)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (enabled : machine.borrowTracker=some tracker)
    (frameTracked : frame.extra.borrowTracker=some borrowFrame)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread?=some thread)
    (body : frame.body=RootBody.reflected.body.body) (location : frame.location=.mir ⟨10,0⟩)
    (size : frame.locals.size=25) (noClocks : frame.extra.dataRace=none)
    (stop : frame.returnContinuation=.stop true) (varargs : frame.vaList=#[])
    (immediate : CopyHelperCleanup.AllImmediate frame) (value : Bool)
    (slot0 : frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool value))),some RootCompilerFacts.boolLayout⟩)
    (destination : frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    ∃ final,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧
      final.stack.frames=#[] := by
  let accounted:=S04FinalReturnRuleAccounting.machine options remaining span frame machine
  have beforeMemory : accounted.memory=machine.memory:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have beforeTracked : accounted.borrowTracker=some tracker:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact enabled
  have activeNow : accounted.threads.activeThread?=some thread:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact active
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList accounted.memory released.memory:=by
    rw [beforeMemory];exact released.plan
  let post : RootState:=⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] frame
    (ActualPopPlan.released accounted released.memory tracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩
  have postUser : post.machine.user=accounted.user:=by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have postMemory : post.machine.memory=released.memory:=by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have addresses : accounted.user.addresses=machine.user.addresses:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨window,pointerEq,idEq,offsetEq,windowBinding⟩:=CurrentCallRootPhysicalWindow.plan tracker.global.protectedTags borrowFrame.protectedTags.toList
    machine.memory released.memory released.plan machine post.machine rfl postMemory (by rw [postUser];exact addresses) place physical binding
  let next : MachineHooks.BorrowState:={tracker with global:=tracker.global.endCall borrowFrame}
  have postEnabled : post.machine.borrowTracker=some next:=by unfold post GenericPopFrame.afterRelevanceAt;split <;> rfl
  have live : released.memory.live.find? (fun row=>row.1==returnId)=some (returnId,window.entry):=by
    rw [←postMemory]
    simpa only [idEq,sameId] using window.live
  have entryEq:window.entry={physical.entry with allocation:=B.allocation.setExtra released.tree}:=
    (Prod.mk.inj (Option.some.inj (live.symm.trans released.live))).2
  have allocation : window.entry.allocation=B.allocation.setExtra released.tree:=congrArg LocalAllocation.allocation entryEq
  have completed:=CurrentCallResourceReleaseWrite.completed_pointer next original originalId parentIssued parentBinding window
    (idEq.trans sameId) ((congrArg UInt64.toNat offsetEq).trans sameOffset) (pointerEq.trans samePointer) rfl
    (by rw [allocation];rfl) (by rw [allocation];rfl)
    (by rw [allocation];exact released.shape) (by rw [allocation];exact released.capacity)
    (by rw [allocation];exact released.parents) (by rw [allocation];exact released.runtime)
    (by rw [allocation];exact released.distinct) (by rw [allocation];exact released.short)
    (by rw [allocation,offsetEq];exact released.owned)
  have resolved:=CurrentCallRootPhysicalWindow.resolve options remaining span post place window windowBinding
  have extras : post.machine.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras:=by
    rw [postUser]
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have readyPost : CurrentCallBoolProtection.WindowReady post.machine window.id window.offset.toNat 1:=by
    rw [idEq,offsetEq];exact ready.transport extras
  have accountedGhost : accounted.user.payload.ghost=false:=by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact model.ghostOff
  have postGhost : post.machine.user.payload.ghost=false:=by rw [postUser];exact accountedGhost
  have postShallow : post.machine.user.payload.validation=.Shallow:=by
    rw [postUser]
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact model.shallow
  have postBackend : post.machine.user.payload.payload.user.backend=.none:=by
    rw [postUser]
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact model.noBackend
  have postRace : post.machine.dataRace=none:=by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> exact model.noDataRace
  have valid0 : (0 : MIR.LocalId)<frame.locals.size:=by rw [size];decide
  have cell0:=Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slot0)
  obtain ⟨updated,returned,_,_,_⟩:=CurrentCallRootReturn.step_of_release_copy options limits remaining span frame accounted tracker borrowFrame
    beforeTracked frameTracked released.memory plan thread activeNow post rfl body location valid0 noClocks accountedGhost stop immediate varargs
    place window windowBinding next postEnabled postRace postBackend postGhost postShallow readyPost completed resolved
    value fuel model.debugOff fuelEq (by rw [cell0]) (by rw [cell0]) destination machine rfl model.unchecked model.noGc model.fixedScheduler
  exact ⟨CanonicalCopy.replaceAllocation post window.id window.entry.kind updated,.next returned (.refl _),rfl,rfl⟩
/-- Backward-compatible uniform-window interface. -/
theorem finish {initial oldTracker data owner returnId returnOffset machine tracker bData bOwner}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (place : MPlaceTy Provenance)
    (original : UniformWindow initial oldTracker data owner returnId returnOffset 1 .ret)
    (B : UniformWindow machine tracker bData bOwner returnId returnOffset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (sameId : physical.id=returnId) (sameOffset : physical.offset.toNat=returnOffset)
    (samePointer : physical.pointer=original.pointer.value)
    (parentIssued : SpatialDelegation machine tracker returnId B.allocation B.precise.completion original.pointer.grant)
    (parentBinding : PointerBinds B.allocation original.pointer)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (released : CurrentCallResourceCurrentRelease.Released B borrowFrame original.pointer.grant physical.offset physical.entry)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (enabled : machine.borrowTracker=some tracker)
    (frameTracked : frame.extra.borrowTracker=some borrowFrame)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread?=some thread)
    (body : frame.body=RootBody.reflected.body.body) (location : frame.location=.mir ⟨10,0⟩)
    (size : frame.locals.size=25) (noClocks : frame.extra.dataRace=none)
    (stop : frame.returnContinuation=.stop true) (varargs : frame.vaList=#[])
    (immediate : CopyHelperCleanup.AllImmediate frame) (value : Bool)
    (slot0 : frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool value))),some RootCompilerFacts.boolLayout⟩)
    (destination : frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    ∃ final,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧
      final.stack.frames=#[] := by
  exact finish_pointer options limits remaining span place original.pointer original.pointerId B physical binding sameId sameOffset samePointer
    parentIssued parentBinding frame borrowFrame released model enabled frameTracked thread active body location size noClocks stop varargs immediate value slot0
    destination ready fuel fuelEq

end
end DuplicatePrefix.CurrentCallResourceRootFinish
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRootFinish" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource root finish dependency {dependency}"
