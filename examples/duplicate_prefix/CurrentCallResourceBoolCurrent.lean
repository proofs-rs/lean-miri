import duplicate_prefix.CurrentCallResourceBoolFacets
import duplicate_prefix.CurrentCallAllocationLicense

namespace DuplicatePrefix.CurrentCallResourceBoolCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallResourceEntryBody
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]


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


def completion : Completion := S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant

def pointer : PointerInstance := ⟨out.physical.id,{C.V.pointer.value with provenance:=.concrete out.physical.id out.boolOutput.tag},out.boolChild⟩

theorem live : out.finalMachine.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
  rw [out.finalMachineEq]
  exact MemoryCopyBridge.live_lookup_replaced
    (ReturnProtection.borrowedState frames (RootFrameData.atSpan out.argsRoot ⟨601⟩).frame out.sourceOutput.frame out.sourceMachine
      ⟨out.sourceOutput.global,tracker.retagMode⟩ out.returnRoom out.physical.id out.physical.entry out.boolOutput.child.tree).machine.memory
    out.physical.id {out.physical.entry with allocation:=out.updated}

theorem present : Present (ActualWorld out.finalMachine) out.physical.id out.updated := by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(out.physical.id,{out.physical.entry with allocation:=out.updated}),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (live out)),rfl⟩

private theorem source_ids : (out.sourceMachine.memory.live.toList.map Prod.fst).Nodup := by
  let kept:=before.memory.live.toList.filter (fun row=>row.1!=id)
  have rows : out.sourceMachine.memory.live.toList=kept++[(id,{out.sourceEntry with allocation:=out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree})] := by
    rw [out.sourceMachineEq]
    change ((before.memory.live.filter (fun row=>row.1!=id)).push (id,{out.sourceEntry with allocation:=out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree})).toList=_
    simp only [Array.toList_push,Array.toList_filter,kept]
  have idsKept : (kept.map Prod.fst).Nodup := by
    simpa only [List.Nodup,List.filter_map,Function.comp_def,kept] using C.state.allocationIds.filter (fun key=>key != id)
  rw [rows,List.map_append]
  apply List.nodup_append.mpr
  refine ⟨idsKept,by simp,?_⟩
  intro key member other singleton same
  have otherEq : other=id := by simpa using singleton
  subst other
  subst key
  obtain ⟨row,rowMem,rowId⟩ := List.mem_map.mp member
  have different := (List.mem_filter.mp rowMem).2
  simp only [rowId,bne_self_eq_false,Bool.false_eq_true] at different

private theorem allocation_eq : out.physical.entry.allocation=(boolRole out).allocation := by
  have physicalPresent : Present (ActualWorld out.sourceMachine) out.physical.id out.physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(out.physical.id,out.physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.physical.live),rfl⟩
  have rolePresent : Present (ActualWorld out.sourceMachine) out.physical.id (boolRole out).allocation := by
    simpa only [out.physicalId] using (boolRole out).present
  have ids : ((ActualWorld out.sourceMachine).toList.map Prod.fst).Nodup := by
    simpa [ActualWorld,List.map_map,Function.comp_def] using source_ids out
  exact CandidateCurrentUniformOwnerWindow.same_id (ActualWorld out.sourceMachine).toList ids out.physical.id _ _ physicalPresent rolePresent

private theorem witness : Nonempty (CurrentCallResourceFnEntry.BorrowWitness (boolRole out) out.boolOutput out.boolChild out.physical.offset 1) := by
  let B:=boolRole out
  have actual : CandidateCurrentFnEntryRaw.operation B.allocation.extra out.sourceOutput.global out.sourceOutput.frame C.physical.id B.pointer.value.provenance out.physical.offset 1=.ok out.boolOutput := by
    simpa only [B,boolRole,Allocation.setExtra,Allocation.mapExtra,out.physicalId] using out.boolActual
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (C.physical.id,out.physical.offset.toNat) ⟨rfl,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  have short : B.allocation.extra.nodes.size<65536 := (role_runtime out).2.2
  obtain ⟨output,child,operation,tag,global,frame,readDone,childDone,lookup,⟨result⟩⟩ := CurrentCallResourceFnEntry.correlated_borrow_selected B (role_runtime out).1 out.sourceOutput.frame out.returnRoom (by rfl)
    (role_runtime out).2.1 short (by omega) out.physical.offset 1 (congrArg UInt64.toNat out.physicalOffset) rfl (by decide) bounds
  have eqOutput : output=out.boolOutput := Except.ok.inj (operation.symm.trans actual)
  subst output
  have ownLookup : out.boolOutput.child.tree.indexOfTag out.boolOutput.tag=some out.boolChild := by
    rw [←out.boolNodeTag]
    exact result.runtime.formed.allocator.nodeTags _ _ out.boolNodeAt
  have equal : child=out.boolChild := Option.some.inj (lookup.symm.trans ownLookup)
  subst child
  exact ⟨result⟩

private theorem issuance :
    SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) C.V.pointer.grant ∧
    SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) out.boolChild := by
  let B:=boolRole out
  obtain ⟨witness⟩ := witness out
  have vacant : B.allocation.extra.nodes.get out.boolChild=none := by
    cases oldAt : B.allocation.extra.nodes.get out.boolChild with
    | none => rfl
    | some old =>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := witness.oldNodes out.boolChild old oldAt
      have same : changed=witness.node := Option.some.inj (changedAt.symm.trans witness.nodeAt)
      have oldTag : old.tag=out.boolOutput.tag := changedTag.symm.trans ((congrArg TreeNode.tag same).trans witness.tag)
      have older:=GeneralBorrowParentTagInvariant.parent_below_fresh B.allocation.extra out.sourceOutput.global (role_runtime out).1 out.boolChild old oldAt
      rw [oldTag,out.boolTag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have parentIssued : SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ C.physical.id out.updated (completion out) B.pointer.grant := by
    apply CurrentCallAllocationLicense.spatial B.issued out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ out.updated
    · simpa only [out.physicalId] using present out
    · rw [out.boolGlobal];rfl
    · exact out.updatedLength.trans (congrArg Allocation.len (allocation_eq out))
    · exact out.updatedSize.trans (congrArg Allocation.byteSize (allocation_eq out))
    · exact out.updatedCapacity.trans witness.capacity
    · intro position root found;rw [out.updatedRoots];exact witness.oldRoots position root found
    · intro index node found
      obtain ⟨next,nextAt,tag,parent,exposure,permission⟩:=witness.oldNodes index node found
      exact ⟨next,by rw [out.updatedNodes];exact nextAt,tag,parent,exposure,permission⟩
    · intro first second edge
      have different : first≠out.boolChild := by
        intro same
        obtain ⟨node,found⟩ := (B.parents.edgeLive first second edge).1
        rw [same,vacant] at found
        cases found
      change (S05ConcreteProtectedChildCompletion.extend B.precise.completion out.boolChild B.pointer.grant).parents[first.toNat]?=_
      rw [S05ConcreteProtectedChildCompletion.old_parent B.precise.completion out.boolChild B.pointer.grant first different (Array.getElem?_eq_some_iff.mp edge).1]
      exact edge
  have parentIssued' : SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) C.V.pointer.grant := by simpa only [out.physicalId,B,boolRole] using parentIssued
  refine ⟨parentIssued',?_⟩
  have childAt : out.updated.extra.nodes.get out.boolChild=some witness.node := by rw [out.updatedNodes];exact witness.nodeAt
  have shape:=witness.constructor
  cases provenance : B.pointer.value.provenance with
  | concrete supplied tag =>
    rw [provenance] at shape
    obtain ⟨parent,parentAt,_,_⟩ := B.binding
    obtain ⟨next,nextAt,_,_,_,_⟩ := witness.oldNodes B.pointer.grant parent parentAt
    apply SpatialDelegation.concrete parentIssued'
    exact .step (.refl _ next (by rw [out.updatedNodes];exact nextAt)) witness.node childAt shape
  | wildcard =>
    rw [provenance] at shape
    obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path out.updated.extra out.afterParents.graph out.boolChild witness.node childAt
    have rootEq : root=out.boolChild := by
      cases path with
      | refl => rfl
      | @step predecessor target earlier node found edge =>
        have same : node=witness.node := Option.some.inj (found.symm.trans childAt)
        rw [same,shape] at edge
        cases edge
    subst root
    have edge:=S05ConcreteProtectedChildCompletion.child_edge out.R.completion out.boolChild C.V.pointer.grant
    obtain ⟨earlier,originRoot,newRoot,originNode,before,originSlot,newRootAt,originAt,exposed,older,originPath⟩ := out.afterParents.virtual position out.boolChild rootSlot C.V.pointer.grant edge
    have same : newRoot=witness.node := Option.some.inj (newRootAt.symm.trans childAt)
    exact SpatialDelegation.wildcard originNode newRoot earlier position originRoot parentIssued' originAt exposed newRootAt (by rw [same];exact shape) older before originSlot rootSlot originPath edge

/-- Original destination parent issuance is retained for use AFTER its actual
child release and whole-frame endCall. No current parent activity is claimed. -/
theorem parent_issued : SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) C.V.pointer.grant := (issuance out).1

theorem issued : SpatialDelegation out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) out.boolChild := (issuance out).2

theorem parent_binding : PointerBinds out.updated C.V.pointer := by
  obtain ⟨node,found,mapped,binding⟩ := out.R.binding
  obtain ⟨w⟩:=witness out
  obtain ⟨next,nextAt,tag,_,exposure,_⟩:=w.oldNodes C.V.pointer.grant node found
  refine ⟨next,by rw [out.updatedNodes];exact nextAt,?_,?_⟩
  · exact out.afterRuntime.formed.allocator.nodeTags _ _ (by rw [out.updatedNodes];exact nextAt)
  · cases provenance : C.V.pointer.value.provenance with
    | concrete id parentTag =>
      simp only [provenance] at binding ⊢
      exact ⟨binding.1,binding.2.trans tag.symm⟩
    | wildcard =>
      simp only [provenance] at binding ⊢
      exact exposure.trans binding

theorem binding : PointerBinds out.updated (pointer out) := by
  refine ⟨out.boolNode,?_,?_,?_⟩
  · rw [out.updatedNodes];exact out.boolNodeAt
  · simpa only [pointer,out.boolNodeTag] using out.afterRuntime.formed.allocator.nodeTags out.boolChild out.boolNode (by rw [out.updatedNodes];exact out.boolNodeAt)
  · exact ⟨rfl,out.boolNodeTag.symm⟩

theorem window (byte : CandidateFreezeContentResources.Byte) (inside : Window out.physical.id out.physical.offset.toNat 1 byte) :
    byte.2<out.updated.len ∧ Embeds out.updated out.boolOutput.global.protectedTags (completion out) out.boolChild byte.2 .exclusive := by
  have bounds:=out.physical.bounds
  have capacityBound:=UInt64.toNat_lt out.physical.capacity
  have endFits : out.physical.offset.toNat+1<2^64 := by omega
  have endEq : (out.physical.offset+1).toNat=out.physical.offset.toNat+1 := by rw [UInt64.toNat_add];change (out.physical.offset.toNat+1)%(2^64)=_;exact Nat.mod_eq_of_lt endFits
  refine ⟨by rw [out.updatedLength,out.physical.bytes];have p:=inside.2;omega,?_⟩
  intro segment member lower upper index node present
  obtain ⟨position,valid,sameSegment⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have interval:=inside.2
  have rights:=out.afterOwned position valid (by omega) (by omega) (by omega) index node present
  have realized:=CandidateCurrentGrantRuntime.realized _ _ (out.afterRuntime.possible position valid index node present) ((out.afterRuntime.formed.profile position valid).present index node present)
  constructor
  · intro below;exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash

private def viewData : Identities := {data with interpretation:={data.interpretation with
    pointers:=data.interpretation.pointers.push (pointer out)
    loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,some C.returnOwner,C.V.loan.depth+1⟩
    precise:=data.interpretation.precise.push (out.physical.id,{C.V.precise with completion:=completion out})}}

private def view : UniformWindow out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ (viewData out)
    data.interpretation.loans.size out.physical.id out.physical.offset.toNat 1 .ret where
  loan:=⟨data.interpretation.pointers.size,some C.returnOwner,C.V.loan.depth+1⟩
  pointer:=pointer out
  allocation:=out.updated
  precise:={C.V.precise with completion:=completion out}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=rfl
  present:=present out
  preciseAt:=by simp [viewData]
  binding:=binding out
  issued:=issued out
  parents:=out.afterParents
  window:=window out

theorem current : ∃ nextData nextOwner,
    ∃ B : UniformWindow out.finalMachine ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner out.physical.id out.physical.offset.toNat 1 .ret,
      B.pointer=pointer out ∧ B.allocation=out.updated ∧ B.precise.completion=completion out :=
  ⟨viewData out,data.interpretation.loans.size,view out,rfl,rfl,rfl⟩

theorem original_address : (pointer out).value.offset=C.physical.pointer.offset := by
  change C.V.pointer.value.offset=C.physical.pointer.offset
  exact congrArg Pointer.offset C.returnPointer.symm

end
end DuplicatePrefix.CurrentCallResourceBoolCurrent
