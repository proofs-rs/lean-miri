import duplicate_prefix.CurrentCallSpatialEntryCurrent
import duplicate_prefix.CurrentCallSpatialEntryBoolPhysical
import duplicate_prefix.CurrentCallSpatialEntryFacts
import duplicate_prefix.CurrentCallSpatialEntryTagSeparation
import duplicate_prefix.CurrentCallPostEntryCheckpoint

/-! The actual paired LIVE spatial entry feeds the common post-entry
checkpoint for arbitrary counts and fixed cell interpretations. Physical copy
readiness, resource views, original return licensing and frame metadata are
derived from the SAME executed entry. This is the live branch of the joint
frontend; the broader dispatcher and finite-conversion branches are separate
consumers of this checkpoint. -/
namespace DuplicatePrefix.CurrentCallJointEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallSpatialEntry CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place limits count}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    (out : Output C limits count)

private theorem same_source_entry (same : out.physical.id=source.backing.id) :
    out.physical.entry.allocation=source.backing.allocation.setExtra (sourceOutput C).child.tree := by
  have live : (CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry).memory.live.find? (fun row=>row.1==source.backing.id)=
      some (source.backing.id,{out.entry with allocation:=out.entry.allocation.setExtra (sourceOutput C).child.tree}) := by
    exact MemoryCopyBridge.live_lookup_replaced before.memory source.backing.id _
  have physical:=out.physical.live
  rw [same] at physical
  have equal := (Prod.mk.inj (Option.some.inj (physical.symm.trans live))).2
  rw [equal,out.allocation]

private theorem source_length : (CurrentCallSpatialEntryCurrent.allocation out).len=source.backing.allocation.len := by
  rw [←CurrentCallSpatialEntryCurrent.entry_allocation out]
  by_cases same : out.physical.id=source.backing.id
  · simp only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_left same]
    rw [out.updatedLength,same_source_entry out same]
    rfl
  · simp only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_right same,out.allocation]
    rfl

private theorem source_size : (CurrentCallSpatialEntryCurrent.allocation out).byteSize=source.backing.allocation.byteSize := by
  rw [←CurrentCallSpatialEntryCurrent.entry_allocation out]
  by_cases same : out.physical.id=source.backing.id
  · simp only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_left same]
    rw [out.updatedSize,same_source_entry out same]
    rfl
  · simp only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_right same,out.allocation]
    rfl

private theorem source_value : (CurrentCallSpatialEntryCurrent.role out).family.value=
    CurrentCallTypedFnEntry.changedPointer source.family.value source.backing.id tracker.global.nextPointerTag := by
  rw [CurrentCallSpatialEntryCurrent.family,out.sourceFamily]
  rfl

private theorem source_binding : CandidateCallBindings.WindowBinding (CurrentCallSpatialEntryCurrent.machine out)
    (CurrentCallSpatialEntryCurrent.role out).family.value (CurrentCallSpatialEntryCurrent.role out).backing.id offset len.toNat := by
  obtain ⟨entry,base,live,cached,storage,room,bounds,address,nonnull,provenance⟩:=C.binding
  have sameEntry : entry=out.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans out.sourceLive))).2
  subst entry
  change CandidateCallBindings.WindowBinding (CurrentCallSpatialEntryCurrent.machine out)
    (CurrentCallSpatialEntryCurrent.role out).family.value out.src.backing.id offset len.toNat
  rw [CurrentCallSpatialEntryCurrent.source_id out]
  refine ⟨CurrentCallSpatialEntryCurrent.sourceEntry out,base,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have found:=CurrentCallSpatialEntryCurrent.live out
    rw [CurrentCallSpatialEntryCurrent.source_id out] at found
    exact found
  · have user : (CurrentCallSpatialEntryCurrent.machine out).user=before.user:=CurrentCallSpatialEntryFacts.user_eq out
    rw [user]
    exact cached
  · rw [CurrentCallSpatialEntryCurrent.entry_allocation out,source_length,source_size,←out.allocation]
    exact storage
  · rw [CurrentCallSpatialEntryCurrent.entry_allocation out,source_length,←out.allocation]
    exact room
  · rw [CurrentCallSpatialEntryCurrent.entry_allocation out,source_length,←out.allocation]
    exact bounds
  · rw [source_value]
    exact address
  · rw [source_value]
    exact nonnull
  · rw [source_value]
    rfl

include C in
private theorem start_eq : (UInt64.ofNat offset).toNat=offset := by
  obtain ⟨entry,base,live,cached,storage,room,bounds,_⟩:=C.binding
  have capacity:=entry.allocation.byteSize.bytes.toNat_lt
  have positive:=C.positive
  have fits : offset<2^64 := by omega
  simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]

private theorem source_data
    (physical : OrdinaryPhysicalValidity.MutU8Slice source.backing.allocation (UInt64.ofNat offset) len)
    (room : source.backing.allocation.len+64<2^64) :
    CurrentCallResourceEntrySourceStorage.Data (CurrentCallSpatialEntryCurrent.allocation out) (UInt64.ofNat offset) len := by
  let valid:=physical.storage.provenance
  have sourceData : CurrentCallResourceEntrySourceStorage.Data source.backing.allocation (UInt64.ofNat offset) len :=
    ⟨physical.slice_storage,physical.storage.byteLength,
      ⟨ProvenanceCopy.WellFormed.pointerOrder valid,ProvenanceCopy.WellFormed.pointerBounds valid,
        ProvenanceCopy.WellFormed.fragmentsAvoidPointers valid,by have count:=valid.fragment_count;omega⟩,
      physical.writable,room⟩
  rw [←CurrentCallSpatialEntryCurrent.entry_allocation out]
  by_cases same : out.physical.id=source.backing.id
  · have beforeData : CurrentCallResourceEntrySourceStorage.Data out.physical.entry.allocation (UInt64.ofNat offset) len := by
      rw [same_source_entry out same]
      exact sourceData.set_extra (sourceOutput C).child.tree
    have mutation : Allocation.writeUninit (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        (out.physical.entry.allocation.setExtra out.updated.extra)=.ok () out.updated := by
      exact CurrentCallSpatialEntryBoolPhysical.mutation out
    obtain ⟨expected,write,maskEq,length,bytes,mutable,extra,maskWF,maskLen,clear⟩:=
      S02SameDestinationUninitInitializedMutation.uninit (out.physical.entry.allocation.setExtra out.updated.extra)
        out.physical.capacity out.physical.offset out.physical.bytes out.physical.size out.physical.mutable
        out.physical.maskValid out.physical.maskLength out.physical.provenanceMap out.physical.bounds
    have equal : expected=out.updated:=(EStateM.Result.ok.inj (write.symm.trans mutation)).2
    subst expected
    change out.updated.len=out.physical.entry.allocation.len at length
    change out.updated.byteSize=out.physical.entry.allocation.byteSize at bytes
    change out.physical.entry.allocation.initializationMask.setRange
      (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) false=.ok out.updated.initializationMask at maskEq
    change out.updated.initializationMask.len=out.physical.entry.allocation.initializationMask.len at maskLen
    change ProvenanceMap.clear (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1))
      (AllocationCopy.snapshot (out.physical.entry.allocation.setExtra out.updated.extra)) (Size.ofBytes 8)
      out.physical.entry.allocation.provenanceMap=.ok () out.updated.provenanceMap at clear
    have fits : out.physical.offset.toNat+1<2^64:=Nat.lt_of_le_of_lt out.physical.bounds out.physical.capacity.toNat_lt
    have endNat : (out.physical.offset+1).toNat=out.physical.offset.toNat+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
    have endpoint:=DuplicatePrefix.source_end (Size.ofBytes out.physical.offset) 1 (by simpa only [Size.ofBytes,UInt64.toNat_one] using fits)
    have fullFits : (UInt64.ofNat offset).toNat+len.toNat<2^64:=
      Nat.lt_of_le_of_lt beforeData.slice.bounds out.physical.entry.allocation.byteSize.bytes.toNat_lt
    have fullNat : (UInt64.ofNat offset+len).toNat=offset+len.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits,start_eq (C:=C)]
    have separate : offset+len.toNat≤out.physical.offset.toNat ∨ out.physical.offset.toNat+1≤offset := by
      by_cases left : offset+len.toNat≤out.physical.offset.toNat
      · exact Or.inl left
      apply Or.inr
      by_cases right : out.physical.offset.toNat+1≤offset
      · exact right
      apply False.elim
      let point:=max offset out.physical.offset.toNat
      exact C.separate (source.backing.id,point)
        ⟨rfl,by dsimp [point];omega,by dsimp [point];have positive:=C.positive;omega⟩
        ⟨((CurrentCallSpatialEntryBoolCurrent.physical_id out).symm.trans same).symm,by rw [←out.physicalOffset];dsimp [point];omega,
          by rw [←out.physicalOffset];dsimp [point];omega⟩
    obtain ⟨mask,maskOK,_,_,initialized⟩:=S02SameDestinationUninitInitializedBits.one_byte_frame
      out.physical.entry.allocation.initializationMask (Size.ofBytes (UInt64.ofNat offset))
      (Size.ofBytes (UInt64.ofNat offset+len)) (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1))
      (Size.ofBytes (out.physical.offset+1)) beforeData.slice.maskValid beforeData.slice.initialized
      (by simp only [Size.ofBytes,fullNat,start_eq (C:=C)];have positive:=C.positive;omega)
      (by rw [beforeData.slice.maskLength];simp only [Size.ofBytes,fullNat];have bound:=beforeData.slice.bounds;rw [start_eq (C:=C)] at bound;exact bound)
      endpoint (by simpa only [Size.ofBytes,allocRange] using endNat)
      (by rw [out.physical.maskLength];simpa only [Size.ofBytes,endNat] using out.physical.bounds)
      (by simpa only [Size.ofBytes,allocRange,fullNat,endNat,start_eq (C:=C)] using separate)
    have maskSame : mask=out.updated.initializationMask:=Except.ok.inj (maskOK.symm.trans maskEq)
    have initializedActual : InitMaskCopy.InitializedOn out.updated.initializationMask
        (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes (UInt64.ofNat offset+len)) := by
      rw [←maskSame];exact initialized
    have snapshotLen : (AllocationCopy.snapshot (out.physical.entry.allocation.setExtra out.updated.extra)).size=out.physical.entry.allocation.len := by
      cases out.physical.entry.allocation
      simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
        Allocation.setExtra,Allocation.mapExtra,Pure.pure,Except.pure,Except.toOption,Option.getD]
    have direct:=S02SameDestinationUninitProvenanceResult.after_clear out.physical.entry.allocation.provenanceMap out.updated.provenanceMap
      (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) _
      (AllocationCopy.snapshot (out.physical.entry.allocation.setExtra out.updated.extra))
      (by rw [snapshotLen];exact out.physical.provenanceMap) (by change (1 : UInt64)≠0;decide) endpoint
      (by rw [snapshotLen,out.physical.bytes];exact out.physical.capacity.toNat_lt) clear
    rw [snapshotLen,←length] at direct
    have result : CurrentCallResourceEntrySourceStorage.Data out.updated (UInt64.ofNat offset) len := by
      refine ⟨⟨beforeData.slice.positive,beforeData.slice.signedSize,?_,maskWF,?_,initializedActual⟩,?_,direct,mutable,?_⟩
      · rw [bytes];exact beforeData.slice.bounds
      · rw [maskLen,bytes];exact beforeData.slice.maskLength
      · rw [length,bytes];exact beforeData.storage
      · rw [length];exact beforeData.storageFits
    simpa only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_left same] using result
  · have result:=sourceData.set_extra (sourceOutput C).child.tree
    simpa only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_right same,out.allocation] using result


private theorem bool_growth : out.updated.extra.nodes.size≤
    (CurrentCallSpatialEntryBoolCurrent.parent out).allocation.extra.nodes.size+1 := by
  let B:=CurrentCallSpatialEntryBoolCurrent.parent out
  have rt:=(spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.old_runtime") out
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first:=(B.window (out.physical.id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  have growth:=CurrentCallResourceBorrowGrowth.operation B rt.1 out.sourceTracked
    ((spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.source_highwater") out)
    (sourceOutput C).frame out.fresh rfl rt.2.1 (by have room:=rt.2.2;change B.allocation.extra.nodes.size+1<65536 at room;omega)
    (by have room:=rt.2.2;change B.allocation.extra.nodes.size+1<65536 at room;omega)
    out.physical.offset 1 rfl rfl (by decide) bounds out.boolOutput out.boolActual
  rw [(spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.write_nodes") out]
  exact growth

private theorem source_nodes (room : source.backing.allocation.extra.nodes.size+8<65536) :
    (CurrentCallSpatialEntryCurrent.allocation out).extra.nodes.size+6<65536 := by
  rw [←CurrentCallSpatialEntryCurrent.entry_allocation out]
  have sourceGrowth:=out.sourceGrowth
  by_cases same : out.physical.id=source.backing.id
  · simp only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_left same]
    have growth:=bool_growth out
    rw [←(spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.allocation_eq") out,same_source_entry out same] at growth
    change out.updated.extra.nodes.size≤(sourceOutput C).child.tree.nodes.size+1 at growth
    omega
  · simp only [CurrentCallSpatialEntryCurrent.sourceEntry,ite_eq_right same]
    change (sourceOutput C).child.tree.nodes.size+6<65536
    omega

private theorem pointer_tags (room : tracker.global.nextPointerTag.value.toNat+8<18446744073709551615) :
    out.boolOutput.global.nextPointerTag.value.toNat+6<18446744073709551615 := by
  have first:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
  have second:=GenericFunctionEntryNumerics.successor_value (sourceOutput C).global.nextPointerTag out.fresh
  rw [out.boolGlobal]
  change (TypedRetagEmpty.successorTag (sourceOutput C).global.nextPointerTag out.fresh).value.toNat+6<18446744073709551615
  rw [second]
  have sourceNext : (sourceOutput C).global.nextPointerTag=TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh:=rfl
  rw [sourceNext,first]
  omega

private theorem replaced_ids {α : Type} (rows : Array (AllocId×α)) (id : AllocId) (value : α)
    (initial : (rows.toList.map Prod.fst).Nodup) :
    (((rows.filter (fun row=>row.1!=id)).push (id,value)).toList.map Prod.fst).Nodup := by
  let kept:=rows.toList.filter (fun row=>row.1!=id)
  have idsKept : (kept.map Prod.fst).Nodup := by
    simpa only [List.Nodup,List.filter_map,Function.comp_def,kept] using initial.filter (fun key=>key !=id)
  simp only [Array.toList_push,Array.toList_filter,List.map_append]
  apply List.nodup_append.mpr
  refine ⟨idsKept,by simp,?_⟩
  intro key member other singleton same
  have otherEq : other=id := by simpa using singleton
  subst other
  subst key
  obtain ⟨row,rowMem,rowId⟩:=List.mem_map.mp member
  have different:=(List.mem_filter.mp rowMem).2
  simp only [rowId,bne_self_eq_false,Bool.false_eq_true] at different

private theorem final_ids : ((CurrentCallSpatialEntryCurrent.machine out).memory.live.toList.map Prod.fst).Nodup := by
  let stage:=CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry
  have initial : (stage.memory.live.toList.map Prod.fst).Nodup:=out.sourceTracked.allocationIds
  have middle:=replaced_ids stage.memory.live out.physical.id
    ({out.physical.entry with allocation:=out.physical.entry.allocation.setExtra out.boolOutput.child.tree}) initial
  exact replaced_ids _ out.physical.id ({out.physical.entry with allocation:=out.updated}) middle

private theorem source_view
    (room : (CurrentCallSpatialEntryCurrent.allocation out).extra.nodes.size+6<65536) :
    ∃current : CurrentCallPostEntryCheckpoint.Source (CurrentCallSpatialEntryCurrent.machine out)
        (CurrentCallSpatialEntryCurrent.held out) offset len,
      current.role.family.value=(CurrentCallSpatialEntryCurrent.role out).family.value ∧
      current.role.backing.allocation=CurrentCallSpatialEntryCurrent.allocation out ∧
      current.role.backing.id=source.backing.id ∧current.tag=(sourceOutput C).tag ∧current.grant=out.child := by
  obtain ⟨node,nodeAt,nodeTag,leaf,hidden,activity⟩:=CurrentCallSpatialEntryCurrent.node out
  let current : CurrentCallPostEntryCheckpoint.Source (CurrentCallSpatialEntryCurrent.machine out)
      (CurrentCallSpatialEntryCurrent.held out) offset len:={
    context:=CurrentCallSpatialEntryCurrent.context out
    role:=CurrentCallSpatialEntryCurrent.role out
    runtime:=CurrentCallSpatialEntryCurrent.runtime out
    distinct:=CurrentCallSpatialEntryCurrent.distinct out
    tag:=(sourceOutput C).tag
    concrete:=by
      have concrete:=CurrentCallSpatialEntryCurrent.concrete out
      rw [←CurrentCallSpatialEntryCurrent.source_id out] at concrete
      exact concrete
    grant:=out.child
    node:=node
    nodeAt:=nodeAt
    nodeTag:=nodeTag
    hidden:=hidden
    activity:=activity
    binding:=source_binding out
    positive:=C.positive
    signedFits:=C.signedFits
    nodes:=room}
  exact ⟨current,rfl,rfl,CurrentCallSpatialEntryCurrent.source_id out,rfl,rfl⟩

private theorem return_view : ∃packet : CurrentCallPostEntryCheckpoint.Return (CurrentCallSpatialEntryCurrent.machine out)
      (CurrentCallSpatialEntryCurrent.held out) place,
    packet.id=out.physical.id ∧packet.offset=out.physical.offset.toNat ∧packet.node.tag=out.boolOutput.tag ∧
      packet.window.allocation=out.updated := by
  obtain ⟨data,owner,B,pointer,allocation,completion⟩:=CurrentCallSpatialEntryBoolCurrent.current out
  obtain ⟨physical,physicalPointer,physicalId,physicalOffset,physicalEntry,binding,profile⟩:=CurrentCallSpatialEntryBoolPhysical.current out
  have sameId : physical.id=out.physical.id:=physicalId.trans (CurrentCallSpatialEntryBoolPhysical.id_eq out).symm
  have sameOffset : physical.offset=out.physical.offset:=physicalOffset.trans (CurrentCallSpatialEntryBoolPhysical.offset_eq out).symm
  have physicalAllocation : physical.entry.allocation=out.updated:=by rw [physicalEntry]
  have grant : B.pointer.grant=out.boolChild:=congrArg PointerInstance.grant pointer
  have facets:=CurrentCallSpatialEntryBoolCurrent.facets out
  let packet : CurrentCallPostEntryCheckpoint.Return (CurrentCallSpatialEntryCurrent.machine out)
      (CurrentCallSpatialEntryCurrent.held out) place:={
    data:=data
    owner:=owner
    id:=out.physical.id
    offset:=out.physical.offset.toNat
    window:=B
    physical:=physical
    physicalId:=sameId
    physicalOffset:=congrArg UInt64.toNat sameOffset
    physicalAllocation:=physicalAllocation.trans allocation.symm
    binding:=by
      have exactBinding : CandidateCallBindings.WindowBinding (CurrentCallSpatialEntryCurrent.machine out) physical.pointer physical.id physical.offset.toNat 1:=binding
      simpa only [sameId,sameOffset] using exactBinding
    original:=(CurrentCallSpatialEntryBoolCurrent.parent out).pointer
    originalId:=(CurrentCallSpatialEntryBoolCurrent.parent out).pointerId
    originalPointer:=(CurrentCallSpatialEntryBoolCurrent.original_pointer out).trans
      (C.returnPointer.symm.trans physicalPointer.symm)
    originalIssued:=by rw [allocation,completion];exact CurrentCallSpatialEntryBoolCurrent.parent_issued out
    originalBinding:=by rw [allocation];exact CurrentCallSpatialEntryBoolCurrent.parent_binding out
    edge:=by rw [completion,grant];exact CurrentCallSpatialEntryBoolCurrent.edge out
    runtime:=by rw [allocation];exact CurrentCallSpatialEntryBoolCurrent.runtime out
    distinct:=by rw [allocation];exact CurrentCallSpatialEntryBoolCurrent.roots out
    short:=by rw [allocation];exact CurrentCallSpatialEntryBoolCurrent.short out
    node:=CurrentCallSpatialEntryBoolCurrent.node out
    nodeAt:=by rw [allocation,grant];exact CurrentCallSpatialEntryBoolCurrent.nodeAt out
    leaf:=facets.1
    hidden:=facets.2.1
    activity:=by rw [allocation,grant,sameOffset];exact facets.2.2
    profile:=by
      have exactProfile : CurrentCallBoolProtection.WindowReady (CurrentCallSpatialEntryCurrent.machine out) physical.id physical.offset.toNat 1:=profile
      simpa only [sameId,sameOffset] using exactProfile}
  exact ⟨packet,rfl,rfl,CurrentCallSpatialEntryBoolCurrent.nodeTag out,allocation⟩

/-- Assemble the common checkpoint from the already executed paired LIVE
spatial entry. All physical and numeric facts below concern the initial packet. -/
private theorem of_live_output (initial : Before) (race : initial.dataRace=none)
    (rootEq : root=CurrentCallSpatialEntryControl.root initial #[] place race)
    (beforeEq : before=CurrentCallPush.preparedMachine initial #[])
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (physicalSource : OrdinaryPhysicalValidity.MutU8Slice source.backing.allocation (UInt64.ofNat offset) len)
    (storageRoom : source.backing.allocation.len+64<2^64)
    (sourceProfile : CurrentCallBoolProtection.WindowReady before source.backing.id offset len.toNat)
    (nodes : source.backing.allocation.extra.nodes.size+8<65536)
    (tags : tracker.global.nextPointerTag.value.toNat+8<18446744073709551615) :
    ∃checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place,
      checkpoint.machine=CurrentCallSpatialEntryCurrent.machine out ∧checkpoint.frame=CurrentCallSpatialEntryFacts.finishedFrame out := by
  obtain ⟨src,valueEq,allocation,sourceId,sourceTag,grant⟩:=source_view out (source_nodes out nodes)
  obtain ⟨output,outputId,outputOffset,outputTag,outputAllocation⟩:=return_view out
  have metadata:=CurrentCallSpatialEntryFacts.metadata out
  have rawBorrow : root.frame.extra.borrowTracker=some ({} : FrameState) := by
    rw [rootEq]
    exact RootEntryFrame.raw_borrow (CurrentCallPush.preparedMachine initial #[]) (.memory place)
      (CallEntryFacts.freshRoot initial).2 tracker (by rw [←beforeEq];exact C.state.enabled)
  have empty : C.borrowFrame={} :=Option.some.inj (C.frameBorrow.symm.trans rawBorrow)
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : (CurrentCallSpatialEntryCurrent.machine out).threads.activeThread?=some thread := by
    have threads : (CurrentCallSpatialEntryCurrent.machine out).threads=before.threads:=CurrentCallSpatialEntryFacts.threads_eq out
    rw [threads,beforeEq]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot initial).1 oldThread 0 oldActive
  have mode : tracker.retagMode=.Default := by
    obtain ⟨actual,enabled,mode⟩:=C.model.defaultTracker
    have equal : tracker=actual:=Option.some.inj (C.state.enabled.symm.trans enabled)
    exact (congrArg MachineHooks.BorrowState.retagMode equal).trans mode
  have copyReady : CurrentCallPostEntryCheckpoint.CopyReady src := by
    refine ⟨?_,?_⟩
    · rw [allocation]
      exact source_data out physicalSource storageRoom
    · rw [sourceId]
      exact sourceProfile.transport (by
        have user : (CurrentCallSpatialEntryCurrent.machine out).user=before.user:=CurrentCallSpatialEntryFacts.user_eq out
        rw [user])
  let borrowFrame:=(C.borrowFrame.addProtector source.backing.id tracker.global.nextPointerTag).addProtector
    out.physical.id (sourceOutput C).global.nextPointerTag
  have sourcePointer : CurrentCallTypedFnEntry.changedPointer source.family.value source.backing.id tracker.global.nextPointerTag=src.role.family.value :=
    (valueEq.trans (source_value out)).symm
  let checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place:={
    machine:=CurrentCallSpatialEntryCurrent.machine out
    tracker:=CurrentCallSpatialEntryCurrent.held out
    tracked:=CurrentCallSpatialEntryFacts.finalTracked out
    mode:=mode
    model:=CurrentCallSpatialEntryFacts.model out
    origins:=CurrentCallSpatialEntryFacts.origins out
    offset:=offset
    source:=src
    sourceEntry:=CurrentCallSpatialEntryCurrent.sourceEntry out
    sourceLive:=by
      rw [sourceId]
      have found:=CurrentCallSpatialEntryCurrent.live out
      rw [CurrentCallSpatialEntryCurrent.source_id out] at found
      exact found
    sourceAllocation:=(CurrentCallSpatialEntryCurrent.entry_allocation out).trans allocation.symm
    copyReady:=copyReady
    output:=output
    sourceBoolTags:=by rw [sourceTag,outputTag];exact CurrentCallSpatialEntryTagSeparation.tags out
    sourceTagAbsentBool:=by
      intro different index node present
      rw [outputAllocation] at present
      have diff : out.physical.id≠source.backing.id:=by simpa only [outputId,sourceId] using different
      simpa only [sourceTag] using CurrentCallSpatialEntryTagSeparation.absent out diff index node present
    separate:=by
      rw [outputId,sourceId,outputOffset]
      intro same byte sourceHit boolHit
      exact C.separate byte sourceHit (by
        simpa only [CurrentCallSpatialEntryBoolCurrent.physical_id out,out.physicalOffset] using boolHit)
    ids:=final_ids out
    tags:=pointer_tags out tags
    frame:=CurrentCallSpatialEntryFacts.finishedFrame out
    body:=metadata.1.trans (by rw [rootEq];rfl)
    identity:=metadata.2.1.trans (by rw [rootEq];rfl)
    callee:=metadata.2.2.1.trans (by rw [rootEq];rfl)
    location:=metadata.2.2.2.2.2.2.2.2
    size:=CurrentCallSpatialEntryFacts.size out
    sourceLocal:=by rw [←sourcePointer];exact CurrentCallSpatialEntryFacts.source_local out
    countLocal:=CurrentCallSpatialEntryFacts.count_local out
    slots:=by intro i;rw [←sourcePointer];exact CurrentCallSpatialEntryFacts.slots out i
    immediate:=CurrentCallSpatialEntryFacts.immediate out
    noClocks:=metadata.2.2.2.2.2.2.1.trans root.noClocks
    track:=(CurrentCallSpatialEntryFacts.track out).trans (by rw [rootEq];rfl)
    relevance:=(CurrentCallSpatialEntryFacts.relevance out).trans (by rw [rootEq];rfl)
    destination:=by rw [metadata.2.2.2.2.1,rootEq];rfl
    stop:=metadata.2.2.2.1.trans (by rw [rootEq];rfl)
    varargs:=metadata.2.2.2.2.2.1.trans (by rw [rootEq];rfl)
    borrowFrame:=borrowFrame
    frameTracked:=metadata.2.2.2.2.2.2.2.1
    protectors:=by
      rw [sourceId,sourceTag,outputId,outputTag,out.boolTag]
      change borrowFrame.protectedTags=#[_,_]
      simp only [borrowFrame,empty,FrameState.addProtector]
      rfl
    thread:=thread
    active:=active
    top:=rfl
    validationFuel:=C.validationFuel
    validationEq:=C.validationEq
    dynamicFuel:=C.dynamicFuel
    dynamicEq:=C.dynamicEq}
  exact ⟨checkpoint,rfl,rfl⟩

/-- The existing actual paired LIVE entry feeds the SAME common body
checkpoint, with arbitrary fixed spatial cell interpretations. -/
theorem live {options remaining span initial tracker ctx offset len source returnOffset ret place}
    (limits : ExecutionMachine.Limits) (race : initial.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallSpatialEntryControl.root initial #[] place race)
      initial tracker ctx offset len source returnOffset ret place)
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (physicalSource : OrdinaryPhysicalValidity.MutU8Slice source.backing.allocation (UInt64.ofNat offset) len)
    (storageRoom : source.backing.allocation.len+64<2^64)
    (sourceProfile : CurrentCallBoolProtection.WindowReady initial source.backing.id offset len.toNat)
    (nodes : source.backing.allocation.extra.nodes.size+8<65536)
    (tags : tracker.global.nextPointerTag.value.toNat+8<18446744073709551615) (count : UInt64) :
    ∃checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span source.family.value len).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) (⟨⟨#[]⟩,initial⟩ : RootState)=
        .ok () (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) := by
  obtain ⟨out,actual⟩:=CurrentCallSpatialEntry.invoke limits race C stackReady count
  have preparedProfile : CurrentCallBoolProtection.WindowReady (CurrentCallPush.preparedMachine initial #[])
      source.backing.id offset len.toNat:=sourceProfile.transport rfl
  obtain ⟨checkpoint,machine,frame⟩:=of_live_output out initial race rfl rfl stackReady
    physicalSource storageRoom preparedProfile nodes tags
  refine ⟨checkpoint,?_⟩
  rw [machine,frame]
  exact actual

end
end DuplicatePrefix.CurrentCallJointEntry

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallJointEntry.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual joint entry/checkpoint dependency {name}: {dependency}"
