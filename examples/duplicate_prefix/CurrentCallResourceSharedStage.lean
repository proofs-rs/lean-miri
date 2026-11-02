import duplicate_prefix.CurrentCallResourcePrefix
import duplicate_prefix.CurrentCallResourceSourceFinal
import duplicate_prefix.CurrentCallResourceBodyReadiness
import duplicate_prefix.CurrentCallResourceDefaultShared

namespace DuplicatePrefix.CurrentCallResourceSharedStage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallResourceNormalization CurrentCallResourceEntryBody CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count)

def machine : Before := RootZeroCompleteState.tick options remaining span out.finalMachine

theorem memory : (machine out).memory=out.finalMachine.memory := by
  unfold machine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]

theorem addresses : (machine out).user.addresses=out.finalMachine.user.addresses := by
  unfold machine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  rfl

theorem model : DuplicatePrefixCallModel.Model options remaining span (machine out) := by
  have original := CurrentCallResourceEntryFacts.model out
  have flags := RootZeroCompleteState.tick_flags options remaining span out.finalMachine
  have unchecked := original.unchecked
  have noGc := original.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold machine RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {original with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

/-- Address normalization uses the original explicit physical binding; it is
not inferred from scalar ownership. The current callee q keeps those bits. -/
theorem source_address : ∃ base : UInt64,
    (machine out).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ ∧
    (CurrentCallResourceSourceAfterBool.pointer out).value=
      Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset)) ∧
    base+UInt64.ofNat offset≠0 := by
  obtain ⟨oldEntry,base,oldLive,cached,extent,headroom,bounds,address,nonnull,_⟩ := C.binding
  have addressSmall := UInt64.toNat_lt W.pointer.value.offset.bytes
  have offsetSmall : offset<2^64 := by omega
  have sumSmall : base.toNat+offset<2^64 := by omega
  have sumEq : (base+UInt64.ofNat offset).toNat=base.toNat+offset := by
    simp only [UInt64.toNat_add,UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetSmall,Nat.mod_eq_of_lt sumSmall]
  have bits : W.pointer.value.offset.bytes=base+UInt64.ofNat offset :=
    UInt64.toNat_inj.mp (address.trans sumEq.symm)
  refine ⟨base,?_,?_,?_⟩
  · rw [addresses out,CurrentCallResourceEntryFacts.user_eq out]
    exact cached
  · change Pointer.new (Provenance.concrete id out.sourceOutput.tag) W.pointer.value.offset = _
    exact congrArg (Pointer.new (Provenance.concrete id out.sourceOutput.tag)) (congrArg Size.ofBytes bits)
  · rw [←bits]
    exact nonnull

theorem source_pair (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count) :
    frame.locals[1]?=some ⟨.live (.immediate
      (CurrentCallTypedSourceCopy.value options remaining span (CurrentCallResourceSourceAfterBool.pointer out).value len).imm),
      some ActualReferenceMetadata.reference⟩ := by
  have stored := shape.slot1.trans (CurrentCallResourceEntryFacts.source_local out)
  have pointer : CurrentCallTypedFnEntry.changedPointer W.pointer.value id tracker.global.nextPointerTag =
      (CurrentCallResourceSourceAfterBool.pointer out).value := by
    rw [CurrentCallResourceSourceAfterBool.pointer,CurrentCallResourceFnEntry.child_pointer,out.sourceTag]
    rfl
  rw [pointer] at stored
  exact stored

theorem tracked : (machine out).borrowTracker=some ⟨out.boolOutput.global,tracker.retagMode⟩ := by
  unfold machine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  exact out.finalTracked

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins (machine out).user.payload.payload.user.types := by
  unfold machine RootZeroCompleteState.tick SourceControl.accounted
  rw [(actual_fields options () (remaining+1) span).terminators]
  exact CurrentCallResourceEntryFacts.origins out

theorem source_bounds : (UInt64.ofNat offset).toNat=offset ∧
    (UInt64.ofNat offset).toNat+len.toNat≤(CurrentCallResourceSourceFinal.entry out).allocation.extra.locations.size.bytes.toNat := by
  have positive:=C.positive
  have first:=CurrentCallResourceSourceFinal.window out (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩
  have last:=CurrentCallResourceSourceFinal.window out (id,offset+len.toNat-1) ⟨rfl,by omega,by omega⟩
  have capacity:=CurrentCallResourceEntryFacets.capacity out
  have limit:=UInt64.toNat_lt (CurrentCallResourceSourceFinal.entry out).allocation.extra.locations.size.bytes
  have length : (CurrentCallResourceSourceFinal.entry out).allocation.len=
      (CurrentCallResourceSourceFinal.entry out).allocation.extra.locations.size.bytes.toNat := by
    rw [capacity.1]
    exact capacity.2
  have fits : offset<2^64 := by rw [length] at first;omega
  have start : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  exact ⟨start,by rw [length] at last;rw [start];omega⟩

private def currentWindow {nextData nextOwner}
    (Q : UniformWindow out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut) :
    UniformWindow (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut where
  loan:=Q.loan
  pointer:=Q.pointer
  allocation:=Q.allocation
  precise:=Q.precise
  loanAt:=Q.loanAt
  pointerAt:=Q.pointerAt
  pointerId:=Q.pointerId
  present:=by simpa only [Present,ActualWorld,memory out] using Q.present
  preciseAt:=Q.preciseAt
  binding:=Q.binding
  issued:=by
    apply CurrentCallAllocationLicense.spatial Q.issued (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ Q.allocation
    · simpa only [Present,ActualWorld,memory out] using Q.present
    · rfl
    · rfl
    · rfl
    · rfl
    · intro position root found;exact found
    · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
    · intro first second edge;exact edge
  parents:=Q.parents
  window:=Q.window

/-- The real nonzero control prefix and current q resources meet at ONE actual
machine. The pure accounting tick changes neither its heap nor q identity. -/
theorem before_shared (nonzero : count≠0) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine)
        (Storage.withCurrent #[] frame (machine out)) ∧
      GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count ∧
      ∃ nextData nextOwner,
        ∃ Q : UniformWindow (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut,
          Q.pointer=CurrentCallResourceSourceAfterBool.pointer out ∧ Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation ∧
          Q.precise.completion=CurrentCallResourceSourceFinal.completion out := by
  obtain ⟨frame,trace,shape⟩ := CurrentCallResourcePrefix.before_shared out nonzero
  obtain ⟨nextData,nextOwner,Q,pointer,allocation,completion⟩ := CurrentCallResourceSourceFinal.current out
  exact ⟨frame,trace,shape,nextData,nextOwner,currentWindow out Q,pointer,allocation,completion⟩

open GeneralBorrowRawSharedExpression RootReferenceInfo

def tree : BorrowTree := (child (CurrentCallResourceSourceFinal.entry out).allocation.extra
  out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
  (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree

def afterMachine (ready : CurrentCallResourceBodyReadiness.Ready C) : Before :=
  {ReferenceBorrowDriver.allocatedMachine (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩
    (CurrentCallResourceBodyReadiness.current_room out ready) with
    memory:=RetagEntry.updatedMemory (machine out).memory id (CurrentCallResourceSourceFinal.entry out) (tree out)}

def afterFrame (frame : CompilerFrameContext.ActualFrame) (valid : RootReferenceFacts.destination true<frame.locals.size)
    (base : UInt64) : CompilerFrameContext.ActualFrame :=
  CopyHelperSteps.advance (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) valid
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id out.boolOutput.global.nextPointerTag) (Size.ofBytes (base+UInt64.ofNat offset))) len (layout true)).imm)
    (RootReferenceFacts.location true)

/-- Lower operational certificates come from the SAME resource Shared
constructor; all frame, metadata and physical bindings are derived here. -/
theorem step_of_steps_with_address (ready : CurrentCallResourceBodyReadiness.Ready C)
    (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count)
    (readDone : (read (CurrentCallResourceSourceFinal.entry out).allocation.extra out.boolOutput.global.protectedTags
      out.sourceOutput.tag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).status=.Completed)
    (childDone : (child (CurrentCallResourceSourceFinal.entry out).allocation.extra out.boolOutput.global.protectedTags
      out.sourceOutput.tag out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).outcome=.ok ()) :
    ∃ base : UInt64,
      (machine out).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ ∧
      (CurrentCallResourceSourceAfterBool.pointer out).value=
        Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset)) ∧
      base+UInt64.ofNat offset≠0 ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] frame (machine out)) =
        (Storage.withCurrent #[] (afterFrame out frame (by rw [shape.size];decide) base) (afterMachine out ready),.ok true) := by
  obtain ⟨base,cached,pointer,nonnull⟩ := source_address out
  have sourceModel:=model out
  obtain ⟨ctx⟩:=ActualReferenceContext.exists_context options remaining span sourceModel.preciseOff sourceModel.implicitOff
  have v1 : (1 : MIR.LocalId)<frame.locals.size := by rw [shape.size];decide
  have v12 : RootReferenceFacts.destination true<frame.locals.size := by rw [shape.size];decide
  have sourceStored:=Option.some.inj ((Array.getElem?_eq_getElem v1).symm.trans (source_pair out frame shape))
  have destStored:=Option.some.inj ((Array.getElem?_eq_getElem v12).symm.trans shape.slot12)
  have baseEq : (config options remaining span).access.runtime.base=(config options (remaining+1) span).access.runtime.base := by
    rw [actual_access_runtime,actual_access_runtime]
  have sourceValue : frame.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset))) len ActualReferenceMetadata.reference).imm) := by
    simpa only [CurrentCallTypedSourceCopy.value,pointer,baseEq] using congrArg LocalState.value sourceStored
  obtain ⟨body,identity,callee,_,_,_,clocks,_,_⟩:=CurrentCallResourceEntryFacts.metadata out
  have actualBody:=shape.body.trans (body.trans root.body)
  have actualIdentity:=shape.identity.trans (identity.trans root.identity)
  have actualCallee:=shape.callee.trans (callee.trans root.callee)
  have query:=RootReferenceFacts.compute_destination #[] frame (machine out) actualBody actualIdentity actualCallee true
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame (machine out))).metadata=PreparedReflection.actual.runtime := sourceModel.metadata
  have absent:=DuplicatePrefixTypeCacheOrigins.slice_not_constructed (machine out).user.payload.payload.user.types metadata (origins out)
  have mode : tracker.retagMode=.Default := by
    obtain ⟨old,enabled,mode⟩:=C.model.defaultTracker
    have same : old=tracker:=Option.some.inj (enabled.symm.trans C.state.enabled)
    subst old
    exact mode
  have live : (machine out).memory.live.find? (fun row=>row.1==id)=some (id,CurrentCallResourceSourceFinal.entry out) := by
    rw [memory out]
    exact CurrentCallResourceSourceFinal.live out
  have positive : (0 : UInt64)<len:=UInt64.lt_iff_toNat_lt.mpr C.positive
  have evaluated:=CurrentCallSharedReference.rvalue_of_steps options limits remaining span ctx sourceModel.debugOff sourceModel.nullComparator .Erased
    C.dynamicFuel C.validationFuel C.dynamicEq C.validationEq base (UInt64.ofNat offset) len id (CurrentCallResourceSourceFinal.entry out)
    positive nonnull C.signedFits #[] frame (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ (tracked out) mode
    (CurrentCallResourceBodyReadiness.current_room out ready) out.sourceOutput.tag (source_bounds out).2 readDone childDone
    (CurrentCallResourceEntryFacets.capacity out).1 (RootReferenceFacts.destination true) (by decide) v1 v12 sourceValue
    (congrArg LocalState.layout sourceStored) (congrArg LocalState.value destStored) (congrArg LocalState.layout destStored)
    query (by rw [shape.extra];exact clocks.trans root.noClocks) sourceModel.ghostOff sourceModel.shallow cached live
    sourceModel.noDataRace metadata absent
  refine ⟨base,cached,pointer,nonnull,?_⟩
  apply CopyHelperSteps.assign_of_actual_rvalue (config options (remaining+1) span) limits #[] frame _ (machine out) _
    (RootReferenceFacts.location true) ⟨RootReferenceFacts.destination true,#[]⟩
    (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) shape.location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.location] using shape.location
  · rw [actualBody]
    exact RootReferenceFacts.statement true
  · exact evaluated

theorem step_of_steps (ready : CurrentCallResourceBodyReadiness.Ready C)
    (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count)
    (readDone : (read (CurrentCallResourceSourceFinal.entry out).allocation.extra out.boolOutput.global.protectedTags
      out.sourceOutput.tag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).status=.Completed)
    (childDone : (child (CurrentCallResourceSourceFinal.entry out).allocation.extra out.boolOutput.global.protectedTags
      out.sourceOutput.tag out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).outcome=.ok ()) :
    ∃ base : UInt64,
      ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] frame (machine out)) =
        (Storage.withCurrent #[] (afterFrame out frame (by rw [shape.size];decide) base) (afterMachine out ready),.ok true) := by
  obtain ⟨base,_,_,_,actual⟩:=step_of_steps_with_address out ready frame shape readDone childDone
  exact ⟨base,actual⟩

end
end DuplicatePrefix.CurrentCallResourceSharedStage
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSharedStage" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource shared stage dependency {dependency}"
