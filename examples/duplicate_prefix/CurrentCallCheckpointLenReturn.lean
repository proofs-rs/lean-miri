import duplicate_prefix.CurrentCallCheckpointLenControl
import duplicate_prefix.CurrentCallCheckpointLenRelease
import duplicate_prefix.LenReturnFromReleaseRuntime

namespace DuplicatePrefix.CurrentCallCheckpointLenReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateCurrentJointCall CurrentCallPostEntryCheckpoint
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend GeneralBorrowForestMixedLenBeforeReturn
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span len count place} (checkpoint : Checkpoint options remaining span len count place)

def caller (frame : CompilerFrameContext.ActualFrame) (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) (base : UInt64):=
  cachedCaller (CurrentCallCheckpointSharedFacts.caller checkpoint frame shape base)
    (by rw [CurrentCallCheckpointSharedFacts.size];decide)

private theorem released_pair (result : BorrowTree.ProtectorReleaseResult)
    (status : result.status=.Released) : result=⟨result.tree,.Released⟩:=by
  cases result
  cases status
  rfl

private theorem cached_slot (frame : CompilerFrameContext.ActualFrame) (valid : 11<frame.locals.size)
    (stored : frame.locals[11]?=some ⟨.live (.immediate .uninit),none⟩) :
    (cachedCaller frame valid).locals[11]?=some ⟨.live (.immediate .uninit),some RootCompilerFacts.usizeLayout⟩ := by
  have fetched:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans stored)
  simp only [cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set_self,fetched]

theorem caller_size (frame : CompilerFrameContext.ActualFrame) (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) (base : UInt64) :
    (caller checkpoint frame shape base).locals.size=25:=by
  simpa only [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using CurrentCallCheckpointSharedFacts.size checkpoint frame shape base

theorem caller_slot (frame : CompilerFrameContext.ActualFrame) (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) (base : UInt64) :
    (caller checkpoint frame shape base).locals[11]?=some ⟨.live (.immediate .uninit),some RootCompilerFacts.usizeLayout⟩:=
  cached_slot _ _ (CurrentCallCheckpointSharedFacts.slot11 checkpoint frame shape base)

structure Result (limits : ExecutionMachine.Limits) where
  frame : CompilerFrameContext.ActualFrame
  shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count
  base : UInt64
  helper : CurrentCallCheckpointLenControl.Returned checkpoint limits frame shape base
  rootFrame : CompilerFrameContext.ActualFrame
  machine : Before
  trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) (Storage.withCurrent #[] rootFrame machine)
  rootEq : rootFrame={PtrMetadataExecution.writeFrame (caller checkpoint frame shape base) 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
    (by rw [caller_size];decide) with location:=.mir ⟨3,0⟩}
  memory : machine.memory=RetagEntry.updatedMemory (CurrentCallCheckpointShared.machine checkpoint).memory
    checkpoint.source.role.backing.id (CurrentCallCheckpointLenControl.entry checkpoint) (CurrentCallCheckpointLenControl.releasedTree checkpoint)
  tracked : machine.borrowTracker=some (CurrentCallCheckpointLenControl.postTracker checkpoint)
  flags : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span helper.machine machine
  active : ∃thread,machine.threads.activeThread?=some thread ∧thread.topUserRelevantFrame=some 0
  sourceLive : machine.memory.live.find? (fun row=>row.1==checkpoint.source.role.backing.id)=some
    (checkpoint.source.role.backing.id,{CurrentCallCheckpointLenControl.entry checkpoint with allocation:=
      ((CurrentCallCheckpointLenControl.entry checkpoint).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree checkpoint))})

/-- Pure return/pop specialization. The actual observer producer supplies this
internal release certificate; the public join derives it on the same tree. -/
theorem of_release (limits : ExecutionMachine.Limits) (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) (base : UInt64)
    (helper : CurrentCallCheckpointLenControl.Returned checkpoint limits frame shape base)
    (trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] checkpoint.frame checkpoint.machine)
      (Storage.withCurrent #[(caller checkpoint frame shape base)] helper.helper helper.machine))
    (release : ((CurrentCallCheckpointLenControl.borrowedTree checkpoint).releaseProtector
      (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag
      (CurrentCallCheckpointLenControl.held checkpoint).global.protectedTags).status=.Released) :
    Nonempty (Result checkpoint limits):=by
  let rootCaller:=caller checkpoint frame shape base
  have size : rootCaller.locals.size=25:=caller_size checkpoint frame shape base
  have valid : 11<rootCaller.locals.size:=by rw [size];decide
  have slot:=caller_slot checkpoint frame shape base
  have cell : rootCaller.locals[11]=⟨.live (.immediate .uninit),some RootCompilerFacts.usizeLayout⟩:=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans slot)
  have clocks : rootCaller.extra.dataRace=none:=CurrentCallCheckpointSharedFacts.noClocks checkpoint frame shape base
  have frameOwned : (CurrentCallCheckpointLenControl.helperFrame checkpoint).protectedTags=
      #[(checkpoint.source.role.backing.id,(CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag)]:=rfl
  have complete : (CurrentCallCheckpointLenControl.borrowedTree checkpoint).releaseProtector
      (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag (CurrentCallCheckpointLenControl.held checkpoint).global.protectedTags=
      ⟨CurrentCallCheckpointLenControl.releasedTree checkpoint,.Released⟩:=by
    exact released_pair _ release
  obtain ⟨rootFrame,machine,step,rootEq,memory,tracked,flags,active⟩:=LenReturnFromReleaseRuntime.step
    options limits remaining span checkpoint.model.debugOff checkpoint.validationFuel checkpoint.validationEq #[] rootCaller helper.helper helper.machine len
    _ helper.facts helper.location helper.returned helper.clocks helper.destination helper.continuation helper.varargs
    valid (congrArg LocalState.value cell) (congrArg LocalState.layout cell) clocks checkpoint.source.role.backing.id
    (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag (CurrentCallCheckpointLenControl.entry checkpoint)
    (CurrentCallCheckpointLenControl.borrowedTree checkpoint) (CurrentCallCheckpointLenControl.releasedTree checkpoint)
    (CurrentCallCheckpointShared.machine checkpoint).memory helper.memory (CurrentCallCheckpointLenControl.held checkpoint)
    (CurrentCallCheckpointLenControl.helperFrame checkpoint) helper.tracked helper.protector frameOwned complete helper.cache helper.race helper.ghost helper.shallow
  refine ⟨⟨frame,shape,base,helper,rootFrame,machine,SuccessfulTrace.append trace (.next step (.refl _)),rootEq,memory,tracked,flags,active rfl,?_⟩⟩
  rw [memory]
  exact StackPopRelease.lookup_commit_same _ _ _ _

/-- Actual common nonzero continuation through the Len helper, its internally
derived observer release, and pop back to root3. -/
theorem invoke (limits : ExecutionMachine.Limits) (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (nonzero : count≠0) : Nonempty (Result checkpoint limits):=by
  obtain ⟨frame,shape,base,helper,trace⟩:=CurrentCallCheckpointLenControl.invoke checkpoint limits budget dispatch nonzero
  exact of_release checkpoint limits frame shape base helper trace (CurrentCallCheckpointLenRelease.completed checkpoint helper)

end
end DuplicatePrefix.CurrentCallCheckpointLenReturn

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenReturn" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common Len return dependency {dependency}"
