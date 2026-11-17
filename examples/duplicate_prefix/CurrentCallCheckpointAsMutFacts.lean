import duplicate_prefix.CurrentCallCheckpointAsMutControl
import duplicate_prefix.CurrentCallCheckpointAsMutReturn

namespace DuplicatePrefix.CurrentCallCheckpointAsMutFacts
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

variable {options remaining span len count place limits}
  {checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output checkpoint limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
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
    returned.root.extra.dataRace=none ∧ returned.root.returnPlace=out.frame.returnPlace ∧
    returned.root.returnContinuation=out.frame.returnContinuation ∧returned.root.vaList=out.frame.vaList := by
  rw [returned.rootEq]
  exact ⟨done.body,done.identity,done.callee,done.clocks,done.root_metadata.1,done.root_metadata.2.1,done.root_metadata.2.2⟩

theorem slot15 : returned.root.locals[15]?=some ⟨.live (.immediate (.scalar
    (CurrentCallCheckpointAsMutReturn.value seed))),some CopyCompilerFacts.destPointerLayout⟩ := by
  rw [returned.rootEq]
  simp only [AsMutPtrReturn.writeFrame,Array.getElem?_set_self,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]

theorem slot16 : ∃ value : Immediate Provenance,returned.root.locals[16]?=some ⟨.live (.immediate value),some ActualReferenceMetadata.reference⟩ := by
  rw [other out done seed returned 16 (by decide)]
  exact ⟨_,done.slot16⟩

theorem count_slot : returned.root.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
  rw [other out done seed returned 2 (by decide),done.count_slot]
  exact CurrentCallCheckpointLenFacts.count_slot checkpoint out.result

theorem unused (index : Fin 25) (lower : 17≤index.val) : returned.root.locals[index.val]?=some ⟨.dead,none⟩ := by
  rw [other out done seed returned index.val (by
    intro same
    have impossible : 17≤15:=same ▸ lower
    exact (by decide : ¬17≤15) impossible)]
  rw [CurrentCallCheckpointDefaultControl.Done.high done index.val lower]
  exact CurrentCallCheckpointLenFacts.unused checkpoint out.result index (by omega) (by omega) (by omega)

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

theorem addresses : returned.machine.user.addresses=out.machine.user.addresses :=
  returned.flags.addresses.trans (seed.addresses.trans (CurrentCallCheckpointDefaultControl.addresses out))

theorem types : returned.machine.user.payload.payload.user.types=out.machine.user.payload.payload.user.types :=
  returned.flags.types.trans (seed.types.trans (CurrentCallCheckpointDefaultControl.types out))

theorem extras : returned.machine.user.payload.payload.user.runtime.extras=out.machine.user.payload.payload.user.runtime.extras :=
  returned.flags.extras.trans (seed.extras.trans (CurrentCallCheckpointDefaultControl.extras out))

theorem model : DuplicatePrefixCallModel.Model options remaining span returned.machine := by
  have old:=CurrentCallCheckpointDefaultControl.model out
  obtain ⟨prior,enabled,mode⟩:=old.defaultTracker
  have same : prior=CurrentCallCheckpointDefaultControl.tracker out:=Option.some.inj (enabled.symm.trans (CurrentCallCheckpointDefaultControl.tracked out))
  subst prior
  refine ⟨old.debugOff,old.preciseOff,old.implicitOff,returned.flags.ghost,returned.flags.shallow,
    ⟨_,returned.tracked,mode⟩,returned.flags.race,returned.flags.backend,?_,returned.flags.fixed,
    returned.flags.unchecked,returned.flags.noGc,old.nullComparator,old.sourceMatches⟩
  rw [returned.flags.types,seed.types]
  exact old.metadata

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins returned.machine.user.payload.payload.user.types := by
  rw [types out done seed returned]
  exact CurrentCallCheckpointLenFacts.origins checkpoint out.result

theorem cached : returned.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==out.source.role.backing.id)=some ⟨out.source.role.backing.id,done.base⟩ := by
  rw [returned.flags.addresses,seed.addresses]
  exact done.cached


abbrev root_metadata := @metadata

theorem track : returned.root.trackCallerArg=none := by
  have eq:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.trackCallerArg) returned.rootEq
  dsimp only [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] at eq
  exact eq.trans (done.input.track.trans (CurrentCallCheckpointLenFacts.track checkpoint out.result))

theorem relevance : returned.root.extra.userRelevance=255 := by
  have eq:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.extra.userRelevance) returned.rootEq
  dsimp only [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] at eq
  have extra:=congrArg MachineHooks.FrameExtra.userRelevance done.input.extra
  exact eq.trans (extra.trans (CurrentCallCheckpointLenFacts.relevance checkpoint out.result))

end
end DuplicatePrefix.CurrentCallCheckpointAsMutFacts
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutFacts" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual AsMut return facts dependency {dependency}"
