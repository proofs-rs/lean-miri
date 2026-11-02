import duplicate_prefix.CurrentCallResourceAcceptedCopy
import duplicate_prefix.RootSuccessToReturn
namespace DuplicatePrefix.CurrentCallResourceAcceptedPrefix
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

    (copied : CurrentCallResourceAcceptedCopy.Result done fresh valid15 seed returned)

/-- Cleanup after the actual accepted byte copy reaches the true Return block. -/
theorem reaches_true :
    ∃ frame,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] copied.frame copied.machine)
      (Storage.withCurrent #[] {frame with location:=.mir ⟨10,0⟩}
        (SourceControl.accounted (config options (remaining+1) span).terminators (Storage.withCurrent #[] frame copied.machine)).machine) ∧
      RootSuccessCleanupFacts.Shape copied.frame frame RootCompilerFacts.boolLayout (.scalar (.fromBool true)):=by
  have valid (index : Fin 25) : index.val<copied.frame.locals.size:=by rw [copied.size];exact index.isLt
  have stored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : copied.frame.locals[index.val]?=some row) : copied.frame.locals[index.val]'(valid index)=row:=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans found)
  have slot0 : copied.frame.locals[0]?=some ⟨.live (.immediate .uninit),none⟩:=by
    rw [copied.keep 0 (by decide),CurrentCallResourceAsMutFacts.other done fresh valid15 seed returned 0 (by decide),done.slot0,
      CurrentCallResourceLenFacts.other result 0 (by decide) (by decide),result.shape.slot0]
    simpa using CurrentCallResourceEntryFacts.slots out ⟨0,by decide⟩
  have slot15:= (copied.keep 15 (by decide)).trans (CurrentCallResourceAsMutFacts.slot15 done fresh valid15 seed returned)
  obtain ⟨body,identity,callee,clocks,_,_,_⟩:=CurrentCallResourceAsMutFacts.metadata done fresh valid15 seed returned
  have mode : (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed).retagMode=.Default:=seed.mode
  exact RootSuccessToReturn.reaches_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span copied.machine copied.model) C.model.debugOff C.validationFuel C.validationEq
    #[] copied.frame copied.machine copied.size _ _ _ _ _
    (congrArg LocalState.value (stored ⟨0,by decide⟩ _ slot0)) (congrArg LocalState.layout (stored ⟨0,by decide⟩ _ slot0))
    (congrArg LocalState.value (stored ⟨15,by decide⟩ _ slot15))
    (congrArg LocalState.value (stored ⟨17,by decide⟩ _ copied.slot17)) (congrArg LocalState.layout (stored ⟨17,by decide⟩ _ copied.slot17))
    (congrArg LocalState.value (stored ⟨18,by decide⟩ _ copied.slot18))
    (congrArg LocalState.value (stored ⟨19,by decide⟩ _ copied.slot19))
    (congrArg LocalState.value (stored ⟨21,by decide⟩ _ copied.slot21))
    (congrArg LocalState.value (stored ⟨24,by decide⟩ _ copied.slot24))
    (copied.body.trans body) (copied.identity.trans identity) (copied.callee.trans callee) copied.location
    ((congrArg (fun extra=>extra.dataRace) copied.extra).trans clocks)
    (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) copied.tracked mode copied.model.ghostOff copied.model.shallow
    copied.model.unchecked copied.model.noGc copied.model.fixedScheduler
end
end DuplicatePrefix.CurrentCallResourceAcceptedPrefix
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedPrefix" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted resource cleanup dependency {dependency}"
