import duplicate_prefix.CurrentCallResourceAsMutFacts
import duplicate_prefix.CurrentCallResourceLenSourceStorage
namespace DuplicatePrefix.CurrentCallResourceCopyInputs
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

private theorem maximum (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).projection.maxSizeOfVal=Size.ofBytes 9223372036854775807:=by
  have fields:=CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨_,_,_,_,projectionEq,_⟩:=fields.placeConstruction
  have same : (config options remaining span).projection.maxSizeOfVal=(config options remaining span).projection.dynamic.maxSizeOfVal:=by rw [projectionEq];rfl
  obtain ⟨_,bound,boundEq,dynamicEq⟩:=fields.projectionDynamic
  rw [same,dynamicEq]
  change bound=Size.ofBytes 9223372036854775807
  exact Except.ok.inj (boundEq.symm.trans (show CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target=
    .ok (Size.ofBytes 9223372036854775807) from rfl))

include C in
theorem bounded (within : count≤len/2) : count≤(config options (remaining+1) span).projection.maxSizeOfVal.bytes:=by
  rw [maximum]
  apply UInt64.le_iff_toNat_le.mpr
  have accepted:=UInt64.le_iff_toNat_le.mp within
  have signed:=C.signedFits
  have divided : (len/2).toNat=len.toNat/2:=UInt64.toNat_div len 2
  rw [divided] at accepted
  change count.toNat≤9223372036854775807
  omega

theorem storage (physical : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (room : W.allocation.len+64<2^64) :
    CurrentCallResourceEntrySourceStorage.Data done.current.allocation (UInt64.ofNat offset) len:=by
  have old:=(CurrentCallResourceLenSourceStorage.of_return out ready result physical room).2
  have qData : CurrentCallResourceEntrySourceStorage.Data done.qWindow.allocation (UInt64.ofNat offset) len:=by
    rw [done.qAllocation]
    exact old
  rw [done.allocation]
  exact qData.set_extra _

include returned in
theorem extras : returned.machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras:=by
  rw [CurrentCallResourceAsMutFacts.extras done fresh valid15 seed returned,result.flags.extras,result.helper.extras]
  have shared : (CurrentCallResourceSharedStage.afterMachine out ready).user.payload.payload.user.runtime.extras=
      out.finalMachine.user.payload.payload.user.runtime.extras:=by
    unfold CurrentCallResourceSharedStage.afterMachine ReferenceBorrowDriver.allocatedMachine CurrentCallResourceSharedStage.machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  rw [shared,CurrentCallResourceEntryFacts.user_eq out]

include returned in
theorem profile (old : CurrentCallBoolProtection.WindowReady before id (UInt64.ofNat offset).toNat len.toNat) :
    CurrentCallBoolProtection.WindowReady returned.machine id (UInt64.ofNat offset).toNat len.toNat:=
  old.transport (extras done fresh valid15 seed returned)
end
end DuplicatePrefix.CurrentCallResourceCopyInputs
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCopyInputs" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource copy inputs dependency {dependency}"
