import duplicate_prefix.CurrentCallResourceBoolCurrent
import duplicate_prefix.GeneralBorrowForestTagHighWaterCtorFrame
namespace DuplicatePrefix.CurrentCallResourceBoolTagSeparation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallResourceNormalization CandidateCurrentGrantResources GeneralBorrowFnEntryRegistration CurrentCallResourceEntryBody
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private def extra (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard

private theorem lookup_exists (mapping : UniKeyMap BorTag) (key : BorTag) (index : UniIndex)
    (member : (key,index)∈mapping.mapping) : ∃ found,mapping.get key=some found := by
  unfold UniKeyMap.get
  cases eq : mapping.mapping.find? (fun row=>row.1==key) with
  | some row => exact ⟨row.2,rfl⟩
  | none =>
    have absent := Array.find?_eq_none.mp eq (key,index) member
    simp at absent

private theorem lookup_member (mapping : UniKeyMap BorTag) (key : BorTag) (index : UniIndex)
    (found : mapping.get key=some index) : ∃ old,(key,old)∈mapping.mapping := by
  unfold UniKeyMap.get at found
  cases eq : mapping.mapping.find? (fun row=>row.1==key) with
  | none => simp [eq] at found
  | some row =>
    have same : row.1=key := by simpa only [beq_iff_eq] using Array.find?_some eq
    exact ⟨row.2,same ▸ Array.mem_of_find?_eq_some eq⟩

private theorem old_lookup_origin (before after : UniKeyMap BorTag) (tag : BorTag)
    (old : ∀ key,tag≠key → after.get key=before.get key) :
    ∀ key index,(key,index)∈after.mapping → key=tag ∨∃ oldIndex,(key,oldIndex)∈before.mapping := by
  intro key index member
  by_cases same : key=tag
  · exact .inl same
  · obtain ⟨found,lookup⟩ := lookup_exists after key index member
    rw [old key (Ne.symm same)] at lookup
    exact .inr (lookup_member before key found lookup)

private theorem insert_origin (before mapping : UniKeyMap BorTag) (tag : BorTag) (index : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh before tag) (fits : before.deassigned.back?=none → before.mapping.size≤4294967295)
    (inserted : before.insert tag=.Inserted mapping index) :
    ∀ key query,(key,query)∈mapping.mapping → key=tag ∨∃old,(key,old)∈before.mapping := by
  cases available : before.deassigned.back? with
  | none =>
    have eq := GeneralBorrowTagMap.insert_append before tag fresh available (fits available)
    rw [eq] at inserted
    cases inserted
    intro key query member
    rcases Array.mem_push.mp member with old | same
    · exact .inr ⟨query,old⟩
    · exact .inl (Prod.mk.inj same).1
  | some free =>
    have eq := GeneralBorrowTagMap.insert_free before tag fresh free available
    rw [eq] at inserted
    cases inserted
    intro key query member
    rcases Array.mem_push.mp member with old | same
    · exact .inr ⟨query,old⟩
    · exact .inl (Prod.mk.inj same).1

private theorem child_of_operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (id : AllocId) (provenance : Provenance) (start amount : UInt64)
    (room : global.nextPointerTag.value < 18446744073709551615) (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation tree global frame id provenance start amount = .ok output) :
    output.child =
      (tree.performBorrowAccessRange (extra provenance)
        (Size.ofBytes start) (Size.ofBytes amount) .Read (registered global frame id room).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes start) (extra provenance) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by
  have allocated := TypedRetagEmpty.allocate_tag global room
  cases provenance with
  | concrete suppliedId tag =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowForestFnEntry.operation,GeneralBorrowForestProtected.read,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl
  | wildcard =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowRawWildcardFnEntryRuntime.operation,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl

/-- Every installed key comes from the original selected tree or the one actual fresh allocation. -/
private theorem key_origin {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    ∀ key index,(key,index)∈output.child.tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨
      ∃oldIndex,(key,oldIndex)∈W.allocation.extra.tagMapping.mapping := by
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,capacity⟩ := CurrentCallResourceFnEntry.prepare_read_selected W runtime frame room exclusive distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change accessed.tree.nodes=W.allocation.extra.nodes at nodes
  change accessed.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change accessed.tree.locations.size=W.allocation.extra.locations.size at capacity
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have afterRoom : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have afterBounds : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have childEq := child_of_operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
  cases provenance : W.pointer.value.provenance with
  | concrete suppliedId parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [provenance] at binds
    have parentAfter : accessed.tree.nodeAt W.pointer.grant=some parentNode := by change accessed.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : accessed.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    let depth := GeneralBorrowStructuralHistoryMutable.depth accessed.tree afterRuntime.formed.toState
    let slot := GeneralBorrowStructuralHistoryMutable.slot accessed.tree afterRuntime.formed.toState W.pointer.grant parentNode parentAfter afterRoom
    have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth afterRuntime.formed.children afterRuntime.formed.covered
      parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter slot start amount nonzero
      afterRuntime.formed.well afterRuntime.formed.fits afterBounds
    have origins := old_lookup_origin accessed.tree.tagMapping
      (GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree parentTag tracker.global.nextPointerTag start amount).tagMapping tracker.global.nextPointerTag metadata.oldLookup
    rw [childEq]
    rw [tags] at origins
    simpa only [GeneralBorrowFreshMetadataChildMutableSlot.result,accessed,registration,provenance,extra] using origins
  | wildcard =>
    obtain ⟨mapping,index,inserted,_,_⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select accessed.tree afterRuntime.formed.toGraphState tracker.global.nextPointerTag
      freshAfter afterRoom (.ReservedFrz false) .None
    have mapped := GeneralBorrowForestTagHighWaterCtorFrame.mapping accessed.tree tracker.global.nextPointerTag mapping index inserted
      (.ReservedFrz false) .None true rfl rfl rfl (Size.ofBytes start) (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside)
    have origins := insert_origin accessed.tree.tagMapping mapping tracker.global.nextPointerTag index freshAfter (by
      intro noFree
      have aligned := GeneralBorrowFreshStagePool.empty_aligned accessed.tree afterRuntime.formed.allocator.accounting noFree
      change accessed.tree.nodes.data.size+1≤4294967295 at afterRoom
      omega) inserted
    rw [childEq]
    simp only [provenance,extra]
    simp only [accessed,registration,provenance,extra] at mapped
    rw [mapped]
    rw [tags] at origins
    exact origins

private theorem window_runtime {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag) :
    DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global ∧ W.allocation.extra.roots.toList.Nodup := by
  have present := W.present
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨actualId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,equal⟩
  have treeEq : entry.allocation.extra=W.allocation.extra := congrArg Allocation.extra equal
  exact ⟨⟨by simpa only [treeEq] using state.formed (actualId,entry) member,
    by simpa only [treeEq] using state.coherent (actualId,entry) member,
    by simpa only [treeEq] using state.possible (actualId,entry) member,
    by simpa only [treeEq] using highwater (actualId,entry) member⟩,
    by simpa only [treeEq] using state.roots (actualId,entry) member⟩

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

include out in
private theorem source_bounds : (UInt64.ofNat offset).toNat=offset ∧
    (UInt64.ofNat offset).toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
  have last := (out.sourceWitness.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have positive := C.positive
  have extent := W.issued.capability.extent
  have treeExtent := W.issued.capability.treeExtent
  have bounded := UInt64.toNat_lt W.allocation.byteSize.bytes
  have fits : offset<2^64 := by omega
  have start : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  exact ⟨start,by rw [start,treeExtent,←extent];omega⟩

private def rolePrecise : PreciseAllocation := {C.V.precise with completion:=out.R.completion}
private def roleData : Identities :=
  {data with interpretation:={data.interpretation with precise:=data.interpretation.precise.push (C.physical.id,rolePrecise out)}}
private def boolRole : UniformWindow out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩ (roleData out)
    C.returnOwner C.physical.id C.physical.offset.toNat 1 .ret where
  loan:=C.V.loan
  pointer:=C.V.pointer
  allocation:=C.V.allocation.setExtra out.R.tree
  precise:=rolePrecise out
  loanAt:=C.V.loanAt
  pointerAt:=C.V.pointerAt
  pointerId:=C.V.pointerId
  present:=out.R.present
  preciseAt:=Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
  binding:=out.R.binding
  issued:=out.R.issued
  parents:=out.R.parents
  window:=out.R.window

private theorem role_runtime : DuplicatePrefixBorrowContract.RuntimeFacts out.R.tree out.sourceOutput.global ∧
    out.R.tree.roots.toList.Nodup ∧ out.R.tree.nodes.size<65536 := by
  by_cases same : C.physical.id=id
  · have trees:=out.sameTree same
    have growth:=CurrentCallResourceEntryFacets.source_growth out
    have room:=C.boolRoom
    rw [C.sameAllocation same] at room
    rw [trees.1]
    refine ⟨out.sourceWitness.runtime,?_,by omega⟩
    obtain ⟨runtime,distinct⟩ := window_runtime W C.state C.highwater
    exact CurrentCallResourceSourceKeyOrigin.roots W runtime C.state C.highwater C.borrowFrame C.fresh (by rfl) distinct C.sourceShort
      (by have h:=C.sourceShort;omega) (UInt64.ofNat offset) len (source_bounds out).1 rfl
      (by intro zero;have p:=C.positive;rw [zero] at p;cases p) (source_bounds out).2 out.sourceOutput out.sourceActual
  · obtain ⟨runtime,distinct⟩ := window_runtime C.V C.state C.highwater
    have current := (GeneralBorrowFnEntryRegistrationRuntime.prepare C.V.allocation.extra tracker.global C.borrowFrame id C.fresh runtime).2.2.2.1
    rw [(out.otherTree same).1]
    refine ⟨?_,distinct,by have room:=C.boolRoom;omega⟩
    rw [out.sourceGlobal]
    exact current


/-- Actual different-allocation Bool protection cannot introduce q's source
tag: old B keys precede it and the one new B key is its strict successor. -/
theorem absent (different : out.physical.id≠id) :
    ∀ index node,out.updated.extra.nodes.get index=some node → node.tag≠out.sourceOutput.tag := by
  let B:=boolRole out
  have actual : CandidateCurrentFnEntryRaw.operation B.allocation.extra out.sourceOutput.global out.sourceOutput.frame C.physical.id B.pointer.value.provenance out.physical.offset 1=.ok out.boolOutput := by
    simpa only [B,boolRole,Allocation.setExtra,Allocation.mapExtra,out.physicalId] using out.boolActual
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (C.physical.id,out.physical.offset.toNat) ⟨rfl,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  have short : B.allocation.extra.nodes.size<65536 := (role_runtime out).2.2
  have origins:=key_origin B (role_runtime out).1 out.sourceOutput.frame out.returnRoom (by rfl) (role_runtime out).2.1 short (by omega)
    out.physical.offset 1 (congrArg UInt64.toNat out.physicalOffset) rfl (by decide) bounds out.boolOutput actual
  have treeEq : B.allocation.extra=C.V.allocation.extra := (out.otherTree (fun same=>different (out.physicalId.trans same))).1
  have originalRuntime:=(window_runtime C.V C.state C.highwater).1
  intro index node found equal
  have mapped:=out.afterRuntime.formed.allocator.nodeTags index node found
  rw [out.updatedTags] at mapped
  obtain ⟨mappedIndex,member⟩:=lookup_member out.boolOutput.child.tree.tagMapping node.tag index mapped
  rcases origins node.tag mappedIndex member with newTag | oldTag
  · have first:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
    have numeric:=congrArg (fun tag : BorTag=>tag.value.toNat) (equal.symm.trans newTag)
    rw [out.sourceGlobal,out.sourceTag] at numeric
    change tracker.global.nextPointerTag.value.toNat=(TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh).value.toNat at numeric
    omega
  · obtain ⟨oldIndex,oldMember⟩:=oldTag
    rw [treeEq] at oldMember
    have older:=originalRuntime.below.mapping (node.tag,oldIndex) oldMember
    rw [equal,out.sourceTag] at older
    exact Nat.lt_irrefl _ older

end
end DuplicatePrefix.CurrentCallResourceBoolTagSeparation
