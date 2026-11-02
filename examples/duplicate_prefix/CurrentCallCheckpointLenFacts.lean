import duplicate_prefix.CurrentCallCheckpointLenReturn

namespace DuplicatePrefix.CurrentCallCheckpointLenFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateCurrentJointCall CurrentCallPostEntryCheckpoint
open LenUncachedFrontend CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

private theorem finish_other (frame : CompilerFrameContext.ActualFrame) (v : 11<frame.locals.size)
    (value : Immediate Provenance) (index : MIR.LocalId) (different : index≠11) :
    ({PtrMetadataExecution.writeFrame (cachedCaller frame v) 11 value (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using v)
      with location:=.mir ⟨3,0⟩} : CompilerFrameContext.ActualFrame).locals[index]?=frame.locals[index]? := by
  simp [PtrMetadataExecution.writeFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Ne.symm different]

private theorem finish_immediate (frame : CompilerFrameContext.ActualFrame) (v : 11<frame.locals.size)
    (value : Immediate Provenance) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate ({PtrMetadataExecution.writeFrame (cachedCaller frame v) 11 value
      (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using v) with location:=.mir ⟨3,0⟩} : CompilerFrameContext.ActualFrame) := by
  apply CopyHelperCleanup.all_immediate_set _ _ _ (by simpa only [LocalPlaces.cachePlaceLayout,Array.size_set] using v) (CopyHelperCleanup.all_immediate_cache frame 11 _ v all)
  intro memory
  simp

variable {options remaining span len count place limits}
    (checkpoint : Checkpoint options remaining span len count place)
    (result : CurrentCallCheckpointLenReturn.Result checkpoint limits)

theorem size : result.rootFrame.locals.size=25 := by
  rw [result.rootEq]
  simpa only [PtrMetadataExecution.writeFrame,Array.size_set] using
    CurrentCallCheckpointLenReturn.caller_size checkpoint result.frame result.shape result.base

theorem other (index : MIR.LocalId) (notLen : index≠11) (notShared : index≠12) :
    result.rootFrame.locals[index]?=result.frame.locals[index]? := by
  rw [result.rootEq]
  exact (finish_other _ _ _ index notLen).trans
    (CurrentCallCheckpointSharedFacts.other checkpoint result.frame result.shape result.base index notShared)

theorem len_slot : result.rootFrame.locals[11]?=some
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ := by
  rw [result.rootEq]
  simp only [CurrentCallCheckpointLenReturn.caller,PtrMetadataExecution.writeFrame,Array.getElem?_set_self,
    cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]

theorem location : result.rootFrame.location=.mir ⟨3,0⟩ := by rw [result.rootEq]

theorem metadata : result.rootFrame.body=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).body ∧
    result.rootFrame.bodyIdentity=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).bodyIdentity ∧
    result.rootFrame.functionInstance=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).functionInstance ∧
    result.rootFrame.extra=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).extra ∧
    result.rootFrame.returnPlace=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).returnPlace ∧
    result.rootFrame.returnContinuation=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).returnContinuation ∧
    result.rootFrame.vaList=(CurrentCallCheckpointSharedFacts.caller checkpoint result.frame result.shape result.base).vaList := by
  rw [result.rootEq]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem root_metadata : result.rootFrame.body=RootBody.reflected.body.body ∧
    result.rootFrame.bodyIdentity=RootBody.reflected.body.identity ∧
    result.rootFrame.functionInstance=RootBody.reflected.functionInstance ∧
    result.rootFrame.extra.dataRace=none ∧
    result.rootFrame.returnPlace=checkpoint.frame.returnPlace ∧
    result.rootFrame.returnContinuation=.stop true ∧result.rootFrame.vaList=#[] := by
  obtain ⟨body,identity,callee,extra,destination,continuation,varargs⟩:=metadata checkpoint result
  exact ⟨body.trans (CurrentCallCheckpointSharedFacts.body checkpoint result.frame result.shape result.base),
    identity.trans (CurrentCallCheckpointSharedFacts.identity checkpoint result.frame result.shape result.base),
    callee.trans (CurrentCallCheckpointSharedFacts.callee checkpoint result.frame result.shape result.base),
    (congrArg (fun e=>e.dataRace) extra).trans (CurrentCallCheckpointSharedFacts.noClocks checkpoint result.frame result.shape result.base),
    destination.trans (CurrentCallCheckpointSharedFacts.destination checkpoint result.frame result.shape result.base),
    continuation.trans (CurrentCallCheckpointSharedFacts.continuation checkpoint result.frame result.shape result.base),
    varargs.trans (CurrentCallCheckpointSharedFacts.varargs checkpoint result.frame result.shape result.base)⟩

theorem count_slot : result.rootFrame.locals[2]?=some
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
  exact (other checkpoint result 2 (by decide) (by decide)).trans (result.shape.slot2.trans checkpoint.countLocal)

theorem zero_slot : result.rootFrame.locals[0]?=some ⟨.live (.immediate .uninit),none⟩ := by
  rw [other checkpoint result 0 (by decide) (by decide),result.shape.slot0]
  simpa using checkpoint.slots ⟨0,by decide⟩

theorem slot13 : result.rootFrame.locals[13]?=some ⟨.live (.immediate .uninit),none⟩ := by
  rw [other checkpoint result 13 (by decide) (by decide),result.shape.keep 13 (by decide)]
  simpa using checkpoint.slots ⟨13,by decide⟩

theorem unused (index : Fin 25) (lower : 13≤index.val) (not13 : index.val≠13) (not14 : index.val≠14) :
    result.rootFrame.locals[index.val]?=some ⟨.dead,none⟩ := by
  have n11 : index.val≠11:=by omega
  have n12 : index.val≠12:=by omega
  rw [other checkpoint result index.val n11 n12,result.shape.keep index.val lower]
  simpa [show ¬14=index.val by omega,show ¬13=index.val by omega,show ¬6=index.val by omega,
    show ¬0=index.val by omega,show ¬2=index.val by omega,show ¬1=index.val by omega] using checkpoint.slots index

theorem slot7 : result.rootFrame.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ :=
  (other checkpoint result 7 (by decide) (by decide)).trans result.shape.slot7
theorem slot8 : result.rootFrame.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ :=
  (other checkpoint result 8 (by decide) (by decide)).trans result.shape.slot8
theorem slot9 : result.rootFrame.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ :=
  (other checkpoint result 9 (by decide) (by decide)).trans result.shape.slot9
theorem slot10 : result.rootFrame.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ :=
  (other checkpoint result 10 (by decide) (by decide)).trans result.shape.slot10

theorem track : result.rootFrame.trackCallerArg=none := by
  rw [result.rootEq]
  exact CurrentCallCheckpointSharedFacts.track checkpoint result.frame result.shape result.base

theorem relevance : result.rootFrame.extra.userRelevance=255 := by
  rw [(metadata checkpoint result).2.2.2.1,CurrentCallCheckpointSharedFacts.extra checkpoint result.frame result.shape result.base]
  exact checkpoint.relevance

theorem immediate : CopyHelperCleanup.AllImmediate result.rootFrame := by
  rw [result.rootEq]
  apply finish_immediate
  exact CopyHelperCleanup.all_immediate_written _ _ _ _ _ result.shape.immediate

theorem model : DuplicatePrefixCallModel.Model options remaining span result.machine := by
  refine ⟨checkpoint.model.debugOff,checkpoint.model.preciseOff,checkpoint.model.implicitOff,result.flags.ghost,result.flags.shallow,
    ⟨_,result.tracked,checkpoint.mode⟩,result.flags.race,result.flags.backend,?_,result.flags.fixed,
    result.flags.unchecked,result.flags.noGc,checkpoint.model.nullComparator,checkpoint.model.sourceMatches⟩
  rw [result.flags.types,result.helper.types]
  exact (CurrentCallCheckpointLenControl.model checkpoint).metadata

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins result.machine.user.payload.payload.user.types := by
  rw [result.flags.types,result.helper.types]
  change DuplicatePrefixTypeCacheOrigins.Origins (CurrentCallCheckpointShared.before checkpoint).user.payload.payload.user.types
  unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  exact checkpoint.origins

end
end DuplicatePrefix.CurrentCallCheckpointLenFacts
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenFacts" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common Len facts dependency {dependency}"
