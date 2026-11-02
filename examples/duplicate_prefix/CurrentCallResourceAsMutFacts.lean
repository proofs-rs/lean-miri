import duplicate_prefix.CurrentCallResourceAsMutInvoke
import duplicate_prefix.CurrentCallResourceAsMutReturn

namespace DuplicatePrefix.CurrentCallResourceAsMutFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem finish_other (frame : CompilerFrameContext.ActualFrame) (valid : 15<frame.locals.size)
    (written : 15<(AsMutUncachedCall.cachedCaller frame valid).locals.size) (value : Immediate Provenance)
    (index : MIR.LocalId) (different : index≠15) :
    ({AsMutPtrReturn.writeFrame (AsMutUncachedCall.cachedCaller frame valid) 15 value written with location:=.mir ⟨7,0⟩} : CompilerFrameContext.ActualFrame).locals[index]?=frame.locals[index]? := by
  simp [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Ne.symm different]

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

include returned in
theorem size : returned.root.locals.size=25 := by
  rw [returned.rootEq]
  simpa only [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using done.size

theorem other (index : MIR.LocalId) (different : index≠15) : returned.root.locals[index]?=done.frame.locals[index]? := by
  rw [returned.rootEq]
  exact finish_other _ _ _ _ index different

theorem location : returned.root.location=.mir ⟨7,0⟩ := by rw [returned.rootEq]

theorem metadata : returned.root.body=RootBody.reflected.body.body ∧
    returned.root.bodyIdentity=RootBody.reflected.body.identity ∧ returned.root.functionInstance=RootBody.reflected.functionInstance ∧
    returned.root.extra.dataRace=none ∧ returned.root.returnPlace=result.rootFrame.returnPlace ∧
    returned.root.returnContinuation=result.rootFrame.returnContinuation ∧returned.root.vaList=result.rootFrame.vaList := by
  rw [returned.rootEq]
  exact ⟨done.body,done.identity,done.callee,done.clocks,done.root_metadata.1,done.root_metadata.2.1,done.root_metadata.2.2⟩

theorem slot15 : returned.root.locals[15]?=some ⟨.live (.immediate (.scalar
    (CurrentCallResourceAsMutReturn.value done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed))),some CopyCompilerFacts.destPointerLayout⟩ := by
  rw [returned.rootEq]
  simp only [AsMutPtrReturn.writeFrame,Array.getElem?_set_self,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]

theorem slot16 : ∃ value : Immediate Provenance,returned.root.locals[16]?=some ⟨.live (.immediate value),some ActualReferenceMetadata.reference⟩ := by
  rw [other done fresh valid15 seed returned 16 (by decide)]
  exact ⟨_,done.slot16⟩

theorem count_slot : returned.root.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
  rw [other done fresh valid15 seed returned 2 (by decide),done.count_slot]
  rw [CurrentCallResourceLenFacts.other result 2 (by decide) (by decide),result.shape.slot2]
  exact CurrentCallResourceEntryFacts.count_local out

theorem unused (index : Fin 25) (lower : 17≤index.val) : returned.root.locals[index.val]?=some ⟨.dead,none⟩ := by
  rw [other done fresh valid15 seed returned index.val (by
    intro same
    have impossible : 17≤15:=same ▸ lower
    exact (by decide : ¬17≤15) impossible)]
  rw [CurrentCallResourceAsMutInvoke.DefaultResult.high (result:=result) done index.val lower]
  exact CurrentCallResourceLenFacts.unused result index (by omega) (by omega) (by omega)

private theorem finish_immediate (frame : CompilerFrameContext.ActualFrame) (valid : 15<frame.locals.size)
    (written : 15<(AsMutUncachedCall.cachedCaller frame valid).locals.size) (value : Immediate Provenance)
    (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate ({AsMutPtrReturn.writeFrame (AsMutUncachedCall.cachedCaller frame valid) 15 value written
      with location:=.mir ⟨7,0⟩} : CompilerFrameContext.ActualFrame) := by
  apply CopyHelperCleanup.all_immediate_set _ _ _ written (CopyHelperCleanup.all_immediate_cache frame 15 _ valid all)
  intro memory
  simp

theorem immediate : CopyHelperCleanup.AllImmediate returned.root := by
  rw [returned.rootEq]
  exact finish_immediate _ _ _ _ done.immediate

theorem addresses : returned.machine.user.addresses=result.machine.user.addresses :=
  returned.flags.addresses.trans (seed.addresses.trans done.addresses)

theorem types : returned.machine.user.payload.payload.user.types=result.machine.user.payload.payload.user.types :=
  returned.flags.types.trans (seed.types.trans done.types)

theorem extras : returned.machine.user.payload.payload.user.runtime.extras=result.machine.user.payload.payload.user.runtime.extras :=
  returned.flags.extras.trans (seed.extras.trans done.extras)

theorem model : DuplicatePrefixCallModel.Model options remaining span returned.machine := by
  have old:=done.model
  obtain ⟨prior,enabled,mode⟩:=old.defaultTracker
  have same : prior=done.nextTracker:=Option.some.inj (enabled.symm.trans done.enabled)
  subst prior
  refine ⟨old.debugOff,old.preciseOff,old.implicitOff,returned.flags.ghost,returned.flags.shallow,
    ⟨_,returned.tracked,mode⟩,returned.flags.race,returned.flags.backend,?_,returned.flags.fixed,
    returned.flags.unchecked,returned.flags.noGc,old.nullComparator,old.sourceMatches⟩
  rw [returned.flags.types,seed.types]
  exact old.metadata

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins returned.machine.user.payload.payload.user.types := by
  rw [types done fresh valid15 seed returned]
  exact CurrentCallResourceLenFacts.origins result

theorem cached : returned.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,done.base⟩ := by
  rw [returned.flags.addresses,seed.addresses]
  exact done.cachedPost


abbrev root_metadata := @metadata

theorem track : returned.root.trackCallerArg=root.frame.trackCallerArg := by
  have actual:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.trackCallerArg) returned.rootEq
  dsimp only [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] at actual
  have defaultTrack:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.trackCallerArg) done.frameEq
  dsimp only [CurrentCallResourceAsMutInvoke.defaultFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] at defaultTrack
  have lenTrack:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.trackCallerArg) result.rootEq
  dsimp only [PtrMetadataExecution.writeFrame,LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout,
    CurrentCallResourceLenInvoke.sharedFrame,CurrentCallResourceSharedStage.afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written] at lenTrack
  exact actual.trans (defaultTrack.trans (done.input.track.trans (lenTrack.trans (result.shape.track.trans (CurrentCallResourceEntryFacts.track out)))))

theorem relevance : returned.root.extra.userRelevance=root.frame.extra.userRelevance := by
  have actual:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.extra) returned.rootEq
  dsimp only [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] at actual
  have defaultExtra:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.extra) done.frameEq
  dsimp only [CurrentCallResourceAsMutInvoke.defaultFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] at defaultExtra
  have extra:=actual.trans (defaultExtra.trans done.input.extra)
  have lenExtra:=(CurrentCallResourceLenFacts.metadata result).2.2.2.1
  rw [extra,lenExtra,result.shape.extra]
  exact CurrentCallResourceEntryFacts.relevance out

end
end DuplicatePrefix.CurrentCallResourceAsMutFacts
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAsMutFacts" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual AsMut return facts dependency {dependency}"
