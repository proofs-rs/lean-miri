import duplicate_prefix.CurrentCallCheckpointShared
import duplicate_prefix.CurrentCallPostEntryControl
import duplicate_prefix.CurrentCallSharedReference

namespace DuplicatePrefix.CurrentCallCheckpointSharedControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallResourceNormalization CurrentCallPostEntryCheckpoint CanonicalConfigFacts ActualReferenceContext RootReferenceInfo
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span len count place} (checkpoint : Checkpoint options remaining span len count place)

private theorem tick_model : DuplicatePrefixCallModel.Model options remaining span (CurrentCallCheckpointShared.before checkpoint) := by
  have model:=checkpoint.model
  have flags:=RootZeroCompleteState.tick_flags options remaining span checkpoint.machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

theorem source_address : ∃ base : UInt64,
    (CurrentCallCheckpointShared.before checkpoint).user.addresses.baseAddr.find? (fun row=>row.allocId==checkpoint.source.role.backing.id)=
      some ⟨checkpoint.source.role.backing.id,base⟩ ∧
    checkpoint.source.role.family.value=Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.source.tag)
      (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)) ∧
    base+UInt64.ofNat checkpoint.offset≠0 := by
  obtain ⟨entry,base,live,cached,storage,room,bounds,address,nonnull,_⟩:=checkpoint.source.binding
  have offsetFit : checkpoint.offset<2^64:=by have small:=checkpoint.source.role.family.value.offset.bytes.toNat_lt;omega
  have sumFit : base.toNat+checkpoint.offset<2^64:=by have small:=checkpoint.source.role.family.value.offset.bytes.toNat_lt;omega
  have sum : (base+UInt64.ofNat checkpoint.offset).toNat=base.toNat+checkpoint.offset:=by
    simp only [UInt64.toNat_add,UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFit,Nat.mod_eq_of_lt sumFit]
  have bits:=UInt64.toNat_inj.mp (address.trans sum.symm)
  refine ⟨base,?_,?_,?_⟩
  · unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact cached
  · calc
      checkpoint.source.role.family.value=Pointer.new checkpoint.source.role.family.value.provenance checkpoint.source.role.family.value.offset:=rfl
      _=Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.source.tag) (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)):=by
        rw [checkpoint.source.concrete]
        exact congrArg (Pointer.new (Provenance.concrete checkpoint.source.role.backing.id checkpoint.source.tag)) (congrArg Size.ofBytes bits)
  · rw [←bits];exact nonnull

def afterFrame (frame : CompilerFrameContext.ActualFrame)
    (valid : RootReferenceFacts.destination true<frame.locals.size) (base : UInt64) : CompilerFrameContext.ActualFrame:=
  CopyHelperSteps.advance (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) valid
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.tracker.global.nextPointerTag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset))) len (layout true)).imm) (RootReferenceFacts.location true)

/-- The shared statement consumes the same checkpoint logical operation and
the existing typed-rvalue/assignment leaves.  Its address evidence stays tied
to the exact base chosen for this actual step. -/
theorem statement (limits : ExecutionMachine.Limits) (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) :
    ∃ base : UInt64,
      (CurrentCallCheckpointShared.before checkpoint).user.addresses.baseAddr.find? (fun row=>row.allocId==checkpoint.source.role.backing.id)=
        some ⟨checkpoint.source.role.backing.id,base⟩ ∧
      checkpoint.source.role.family.value=Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.source.tag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)) ∧base+UInt64.ofNat checkpoint.offset≠0 ∧
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent #[] frame (CurrentCallCheckpointShared.before checkpoint))=
        (Storage.withCurrent #[] (afterFrame checkpoint frame (by rw [shape.size];decide) base)
          (CurrentCallCheckpointShared.machine checkpoint),.ok true) := by
  obtain ⟨base,cached,pointer,nonnull⟩:=source_address checkpoint
  have model:=tick_model checkpoint
  obtain ⟨ctx⟩:=ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  have valid1 : (1 : MIR.LocalId)<frame.locals.size:=by rw [shape.size];decide
  have valid12 : RootReferenceFacts.destination true<frame.locals.size:=by rw [shape.size];decide
  have sourceStored:=Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (shape.slot1.trans checkpoint.sourceLocal))
  have destStored:=Option.some.inj ((Array.getElem?_eq_getElem valid12).symm.trans shape.slot12)
  have baseEq : (config options remaining span).access.runtime.base=(config options (remaining+1) span).access.runtime.base:=by
    rw [actual_access_runtime,actual_access_runtime]
  have sourceValue : frame.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.source.tag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset))) len ActualReferenceMetadata.reference).imm):=by
    simpa only [CurrentCallTypedSourceCopy.value,pointer,baseEq] using congrArg LocalState.value sourceStored
  have body:=shape.body.trans checkpoint.body
  have identity:=shape.identity.trans checkpoint.identity
  have callee:=shape.callee.trans checkpoint.callee
  have query:=RootReferenceFacts.compute_destination #[] frame (CurrentCallCheckpointShared.before checkpoint) body identity callee true
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (CurrentCallCheckpointShared.before checkpoint).user.payload.payload.user.types:=by
    unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact checkpoint.origins
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame (CurrentCallCheckpointShared.before checkpoint))).metadata=
      PreparedReflection.actual.runtime:=model.metadata
  have absent:=DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata origins
  have enabled : (CurrentCallCheckpointShared.before checkpoint).borrowTracker=some checkpoint.tracker:=by
    unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact checkpoint.tracked
  have live : (CurrentCallCheckpointShared.before checkpoint).memory.live.find? (fun row=>row.1==checkpoint.source.role.backing.id)=
      some (checkpoint.source.role.backing.id,checkpoint.sourceEntry):=by
    unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact checkpoint.sourceLive
  have capacity : checkpoint.sourceEntry.allocation.extra.locations.size=checkpoint.sourceEntry.allocation.byteSize:=by
    rw [checkpoint.sourceAllocation]
    let byte:=(checkpoint.source.role.backing.id,checkpoint.offset)
    have inside : Window checkpoint.source.role.backing.id checkpoint.offset len.toNat byte:=⟨rfl,Nat.le_refl _,by have p:=checkpoint.source.positive;dsimp only [byte];omega⟩
    obtain ⟨i,cell⟩:=checkpoint.source.role.covered byte inside
    exact (checkpoint.source.role.roles i ⟨byte,inside,cell⟩).issued.capability.treeExtent
  have operation:=CurrentCallCheckpointShared.operation checkpoint
  have bounds:=CurrentCallCheckpointShared.bounds checkpoint
  have evaluated:=CurrentCallSharedReference.rvalue_of_steps options limits remaining span ctx model.debugOff model.nullComparator .Erased
    checkpoint.dynamicFuel checkpoint.validationFuel checkpoint.dynamicEq checkpoint.validationEq base (UInt64.ofNat checkpoint.offset) len
    checkpoint.source.role.backing.id checkpoint.sourceEntry (UInt64.lt_iff_toNat_lt.mpr checkpoint.source.positive) nonnull checkpoint.source.signedFits
    #[] frame (CurrentCallCheckpointShared.before checkpoint) checkpoint.tracker enabled checkpoint.mode (CurrentCallCheckpointShared.room checkpoint)
    checkpoint.source.tag (by rw [checkpoint.sourceAllocation];exact bounds)
    (by rw [checkpoint.sourceAllocation];exact operation.1) (by rw [checkpoint.sourceAllocation];exact operation.2.1) capacity
    (RootReferenceFacts.destination true) (by decide) valid1 valid12 sourceValue (congrArg LocalState.layout sourceStored)
    (congrArg LocalState.value destStored) (congrArg LocalState.layout destStored) query
    (by rw [shape.extra];exact checkpoint.noClocks) model.ghostOff model.shallow cached live model.noDataRace metadata absent
  refine ⟨base,cached,pointer,nonnull,?_⟩
  apply CopyHelperSteps.assign_of_actual_rvalue (config options (remaining+1) span) limits #[] frame _
    (CurrentCallCheckpointShared.before checkpoint) _ (RootReferenceFacts.location true) ⟨RootReferenceFacts.destination true,#[]⟩
    (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) shape.location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.location] using shape.location
  · rw [body];exact RootReferenceFacts.statement true
  · have machineEq : {ReferenceBorrowDriver.allocatedMachine (CurrentCallCheckpointShared.before checkpoint) checkpoint.tracker
        (CurrentCallCheckpointShared.room checkpoint) with memory:=(RetagEntry.updatedMemory
          (CurrentCallCheckpointShared.before checkpoint).memory checkpoint.source.role.backing.id checkpoint.sourceEntry
          (GeneralBorrowRawSharedExpression.child checkpoint.sourceEntry.allocation.extra checkpoint.tracker.global.protectedTags
            checkpoint.source.tag checkpoint.tracker.global.nextPointerTag (UInt64.ofNat checkpoint.offset) len .VisitChildrenOfAccessed).tree)}=
        CurrentCallCheckpointShared.machine checkpoint:=by
      simp only [CurrentCallCheckpointShared.machine,CurrentCallSpatialSharedInstall.machine,CurrentCallSpatialSharedInstall.tree]
      rw [checkpoint.sourceAllocation]
      rfl
    dsimp only at evaluated
    rw [machineEq] at evaluated
    exact evaluated

/-- One common actual nonzero body prefix, for uniform or spatial source
resources, retaining the correlated physical address for the Len call. -/
theorem invoke (limits : ExecutionMachine.Limits) (nonzero : count≠0) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      ∃ shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count,
        ∃ base : UInt64,
          (CurrentCallCheckpointShared.before checkpoint).user.addresses.baseAddr.find? (fun row=>row.allocId==checkpoint.source.role.backing.id)=
            some ⟨checkpoint.source.role.backing.id,base⟩ ∧
          checkpoint.source.role.family.value=Pointer.new (.concrete checkpoint.source.role.backing.id checkpoint.source.tag)
            (Size.ofBytes (base+UInt64.ofNat checkpoint.offset)) ∧base+UInt64.ofNat checkpoint.offset≠0 ∧
          SuccessfulTrace.Trace (config options (remaining+1) span) limits
            (Storage.withCurrent #[] checkpoint.frame checkpoint.machine)
            (Storage.withCurrent #[] (afterFrame checkpoint frame (by rw [shape.size];decide) base)
              (CurrentCallCheckpointShared.machine checkpoint)) := by
  obtain ⟨frame,trace,shape⟩:=CurrentCallPostEntryControl.before_shared checkpoint limits nonzero
  obtain ⟨base,cached,pointer,nonnull,actual⟩:=statement checkpoint limits frame shape
  exact ⟨frame,shape,base,cached,pointer,nonnull,SuccessfulTrace.append trace (.next actual (.refl _))⟩

end
end DuplicatePrefix.CurrentCallCheckpointSharedControl

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointSharedControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common shared control dependency {dependency}"
