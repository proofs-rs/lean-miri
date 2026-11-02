import duplicate_prefix.CurrentCallCheckpointRoot3
import duplicate_prefix.GenericLenAcceptedPrelude
namespace DuplicatePrefix.CurrentCallCheckpointAcceptedControl
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

theorem invoke (nonzero : count≠0) (within : count≤len/2) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] out.result.rootFrame out.result.machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span out.result.machine)))) ∧
      (frame.body=out.result.rootFrame.body ∧ frame.bodyIdentity=out.result.rootFrame.bodyIdentity ∧
      frame.functionInstance=out.result.rootFrame.functionInstance ∧ frame.extra=out.result.rootFrame.extra ∧
      frame.returnPlace=out.result.rootFrame.returnPlace ∧ frame.returnContinuation=out.result.rootFrame.returnContinuation ∧
      frame.vaList=out.result.rootFrame.vaList ∧ frame.localsIdentity=out.result.rootFrame.localsIdentity ∧frame.trackCallerArg=out.result.rootFrame.trackCallerArg ∧
      frame.locals.size=25 ∧ frame.location=.mir ⟨6,7⟩ ∧
      frame.locals[1]?=out.result.rootFrame.locals[1]? ∧ frame.locals[2]?=out.result.rootFrame.locals[2]? ∧
      frame.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧ CopyHelperCleanup.AllImmediate frame) ∧
      GenericLenAcceptedPrelude.FrameFacts out.result.rootFrame frame := by
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
  have s15:=fetched (valid ⟨15,by decide⟩) (CurrentCallCheckpointLenFacts.unused checkpoint out.result ⟨15,by decide⟩ (by decide) (by decide) (by decide))
  have s16:=fetched (valid ⟨16,by decide⟩) (CurrentCallCheckpointLenFacts.unused checkpoint out.result ⟨16,by decide⟩ (by decide) (by decide) (by decide))
  obtain ⟨body,identity,callee,clocks,rest⟩:=CurrentCallCheckpointLenFacts.root_metadata checkpoint out.result
  have model:=CurrentCallCheckpointLenFacts.model checkpoint out.result
  obtain ⟨tracker,tracked,mode⟩:=model.defaultTracker
  have countPositive : (0 : UInt64)<count := UInt64.lt_iff_toNat_lt.mpr (by
    have notzero : count.toNat≠0:=by intro eq;exact nonzero (UInt64.toNat_inj.mp eq)
    simp only [UInt64.toNat_zero];omega)
  obtain ⟨frame,⟨trace,details⟩,facts⟩ := GenericLenAcceptedPrelude.executes_full options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span out.result.machine model)
    model.debugOff checkpoint.validationFuel checkpoint.validationEq out.result.rootFrame out.result.machine len count countPositive within sz value
    (congrArg LocalState.value s12) (congrArg LocalState.value s13) (congrArg LocalState.layout s13)
    (congrArg LocalState.value s0) (congrArg LocalState.layout s0) (congrArg LocalState.value s7) (congrArg LocalState.layout s7)
    (congrArg LocalState.value s15) (congrArg LocalState.layout s15) (congrArg LocalState.value s16) (congrArg LocalState.layout s16)
    (congrArg LocalState.value s8) (congrArg LocalState.layout s8)
    (congrArg LocalState.value s9) (congrArg LocalState.layout s9)
    (congrArg LocalState.value s10) (congrArg LocalState.layout s10)
    (congrArg LocalState.value s11) (congrArg LocalState.layout s11)
    body identity callee (CurrentCallCheckpointLenFacts.location checkpoint out.result) (CurrentCallCheckpointLenFacts.immediate checkpoint out.result) clocks tracker tracked mode
    model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
  exact ⟨frame,trace,details,facts⟩



theorem source_pair : out.result.rootFrame.locals[1]?=some ⟨.live (.immediate
    (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      checkpoint.source.role.family.value len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ := by
  have pair := (CurrentCallCheckpointLenFacts.other checkpoint out.result 1 (by decide) (by decide)).trans
    (out.result.shape.slot1.trans checkpoint.sourceLocal)
  simpa only [CurrentCallTypedSourceCopy.value] using pair

/-- The actual frame boundary before Default-mut, independent of its resource origin cells. -/
structure Input where
  frame : CompilerFrameContext.ActualFrame
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] out.frame out.machine)
    (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span
      (RootZeroCompleteState.tick options remaining span out.machine)))
  body : frame.body=RootBody.reflected.body.body
  identity : frame.bodyIdentity=RootBody.reflected.body.identity
  callee : frame.functionInstance=RootBody.reflected.functionInstance
  clocks : frame.extra.dataRace=none
  location : frame.location=.mir ⟨6,7⟩
  size : frame.locals.size=25
  source : frame.locals[1]?=some ⟨.live (.immediate
    (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      checkpoint.source.role.family.value len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩
  dest15 : frame.locals[15]?=some ⟨.live (.immediate .uninit),none⟩
  dest16 : frame.locals[16]?=some ⟨.live (.immediate .uninit),none⟩
  extra : frame.extra=out.frame.extra
  returnPlace : frame.returnPlace=out.frame.returnPlace
  continuation : frame.returnContinuation=out.frame.returnContinuation
  vaList : frame.vaList=out.frame.vaList
  second : frame.locals[2]?=out.frame.locals[2]?
  facts : GenericLenAcceptedPrelude.FrameFacts out.frame frame
  track : frame.trackCallerArg=out.frame.trackCallerArg
  immediate : CopyHelperCleanup.AllImmediate frame

theorem input (nonzero : count≠0) (within : count≤len/2) : Nonempty (Input out) := by
  obtain ⟨frame,trace,⟨body,identity,callee,extra,returnPlace,continuation,varargs,localsId,callerArg,size,location,source,second,dest15,dest16,immediate⟩,facts⟩ :=
    invoke out nonzero within
  obtain ⟨rootBody,rootIdentity,rootCallee,rootClocks,rest⟩ := CurrentCallCheckpointLenFacts.root_metadata checkpoint out.result
  exact ⟨⟨frame,trace,body.trans rootBody,identity.trans rootIdentity,callee.trans rootCallee,
    (congrArg MachineHooks.FrameExtra.dataRace extra).trans rootClocks,location,size,
    source.trans (source_pair out),dest15,dest16,extra,returnPlace,continuation,varargs,second,facts,callerArg,immediate⟩⟩


def before := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span out.machine)

theorem source_address : ∃ base : UInt64,
    (before out).user.addresses.baseAddr.find? (fun row=>row.allocId==out.source.role.backing.id)=
      some ⟨out.source.role.backing.id,base⟩ ∧
    out.source.role.family.value=Pointer.new (.concrete out.source.role.backing.id checkpoint.source.tag)
      (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)) ∧
    base+UInt64.ofNat checkpoint.offset≠0 := by
  obtain ⟨entry,base,live,cached,storage,room,bounds,address,nonnull,_⟩:=out.source.binding
  have offsetFit : checkpoint.offset<2^64:=by have small:=out.source.role.family.value.offset.bytes.toNat_lt;omega
  have sumFit : base.toNat+checkpoint.offset<2^64:=by have small:=out.source.role.family.value.offset.bytes.toNat_lt;omega
  have sum : (base+UInt64.ofNat checkpoint.offset).toNat=base.toNat+checkpoint.offset:=by
    simp only [UInt64.toNat_add,UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFit,Nat.mod_eq_of_lt sumFit]
  have bits:=UInt64.toNat_inj.mp (address.trans sum.symm)
  refine ⟨base,?_,?_,?_⟩
  · unfold before RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cached
  · calc
      out.source.role.family.value=Pointer.new out.source.role.family.value.provenance out.source.role.family.value.offset:=rfl
      _=Pointer.new (.concrete out.source.role.backing.id checkpoint.source.tag) (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)):=by
        rw [out.source.concrete]
        exact congrArg (Pointer.new (Provenance.concrete out.source.role.backing.id checkpoint.source.tag)) (congrArg Size.ofBytes bits)
  · rw [←bits];exact nonnull

end
end DuplicatePrefix.CurrentCallCheckpointAcceptedControl
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAcceptedControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual rejected prefix dependency {dependency}"
