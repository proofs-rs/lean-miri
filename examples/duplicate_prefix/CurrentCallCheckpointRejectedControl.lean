import duplicate_prefix.CurrentCallCheckpointRoot3
import duplicate_prefix.RootRejectedPrefix
namespace DuplicatePrefix.CurrentCallCheckpointRejectedControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
private theorem fetched {frame : CompilerFrameContext.ActualFrame} {index : Nat} {slot : LocalState Provenance LocalLayout}
    (valid : index<frame.locals.size) (eq : frame.locals[index]?=some slot) : frame.locals[index]=slot :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans eq)
private theorem cached_write_other (frame : CompilerFrameContext.ActualFrame) (valid : 11<frame.locals.size)
    (value : Immediate Provenance) (index : Nat) (different : index≠11) :
    (PtrMetadataExecution.writeFrame (LenUncachedFrontend.cachedCaller frame valid) 11 value
      (by simpa only [LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using valid)).locals[index]?=frame.locals[index]?:=by
  simp [PtrMetadataExecution.writeFrame,LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout,Ne.symm different]

private theorem shared_slot {options remaining span len count place limits}
    (checkpoint : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result checkpoint limits) :
    ∃value layout,result.rootFrame.locals[12]?=some ⟨.live (.immediate value),some layout⟩:=by
  refine ⟨CurrentCallCheckpointSharedFacts.readerValue checkpoint result.base,SharedReferenceMetadata.sharedLayout,?_⟩
  rw [result.rootEq]
  exact (cached_write_other _ _ _ 12 (by decide)).trans
    (CurrentCallCheckpointSharedFacts.slot12 checkpoint result.frame result.shape result.base)

variable {options remaining span len count place limits}
    {checkpoint : Checkpoint options remaining span len count place}
    (out : CurrentCallCheckpointRoot3.Output checkpoint limits)

theorem invoke (gt : count>len/2) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] out.result.rootFrame out.result.machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span out.result.machine)))) ∧
      frame.body=out.result.rootFrame.body ∧ frame.bodyIdentity=out.result.rootFrame.bodyIdentity ∧
      frame.functionInstance=out.result.rootFrame.functionInstance ∧ frame.extra=out.result.rootFrame.extra ∧
      frame.returnPlace=out.result.rootFrame.returnPlace ∧ frame.returnContinuation=out.result.rootFrame.returnContinuation ∧
      frame.vaList=out.result.rootFrame.vaList ∧ frame.localsIdentity=out.result.rootFrame.localsIdentity ∧frame.locals.size=25 ∧
      frame.location=.mir ⟨10,0⟩ ∧
      frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate frame := by
  have sz:=CurrentCallCheckpointLenFacts.size checkpoint out.result
  have valid (index : Fin 25) : index.val<out.result.rootFrame.locals.size := by rw [sz];exact index.isLt
  obtain ⟨value,layout,shared⟩:=shared_slot checkpoint out.result
  have s12:=fetched (valid ⟨12,by decide⟩) shared
  have s13:=fetched (valid ⟨13,by decide⟩) (CurrentCallCheckpointLenFacts.slot13 checkpoint out.result)
  have s0:=fetched (valid ⟨0,by decide⟩) (CurrentCallCheckpointLenFacts.zero_slot checkpoint out.result)
  have s7:=fetched (valid ⟨7,by decide⟩) (CurrentCallCheckpointLenFacts.slot7 checkpoint out.result)
  have s8:=fetched (valid ⟨8,by decide⟩) (CurrentCallCheckpointLenFacts.slot8 checkpoint out.result)
  have s9:=fetched (valid ⟨9,by decide⟩) (CurrentCallCheckpointLenFacts.slot9 checkpoint out.result)
  have s10:=fetched (valid ⟨10,by decide⟩) (CurrentCallCheckpointLenFacts.slot10 checkpoint out.result)
  have s11:=fetched (valid ⟨11,by decide⟩) (CurrentCallCheckpointLenFacts.len_slot checkpoint out.result)
  obtain ⟨body,identity,callee,clocks,rest⟩:=CurrentCallCheckpointLenFacts.root_metadata checkpoint out.result
  have model:=CurrentCallCheckpointLenFacts.model checkpoint out.result
  obtain ⟨tracker,tracked,mode⟩:=model.defaultTracker
  exact RootRejectedPrefix.executes options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span out.result.machine model)
    model.debugOff checkpoint.validationFuel checkpoint.validationEq out.result.rootFrame out.result.machine len count gt sz value
    (congrArg LocalState.value s12) (congrArg LocalState.value s13) (congrArg LocalState.layout s13)
    (congrArg LocalState.value s0) (congrArg LocalState.layout s0) (congrArg LocalState.value s7)
    (congrArg LocalState.value s8) (congrArg LocalState.layout s8)
    (congrArg LocalState.value s9) (congrArg LocalState.layout s9)
    (congrArg LocalState.value s10) (congrArg LocalState.layout s10)
    (congrArg LocalState.value s11) (congrArg LocalState.layout s11)
    body identity callee (CurrentCallCheckpointLenFacts.location checkpoint out.result) (CurrentCallCheckpointLenFacts.immediate checkpoint out.result) clocks tracker tracked mode
    model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
end
end DuplicatePrefix.CurrentCallCheckpointRejectedControl
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointRejectedControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual rejected prefix dependency {dependency}"
