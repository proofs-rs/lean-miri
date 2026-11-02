import duplicate_prefix.CurrentCallSpatialEntry
import duplicate_prefix.CurrentCallResourceBoolCurrent
import duplicate_prefix.GeneralBorrowEffectfulRetagCausalOrder
namespace DuplicatePrefix.CurrentCallSpatialEntryBoolCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallSpatialEntry
open CurrentCallSpatialCover CurrentCallSpatialJointInstall
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


private theorem selected_facets {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree (registered tracker.global frame id room).1 ∧
    output.child.tree.locations.size=W.allocation.extra.locations.size ∧
    ∃ child node, output.child.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      output.child.tree.nodeAt child=some node ∧ node.tag=tracker.global.nextPointerTag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write start (start+amount) := by
  have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount := by
    exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read_selected W runtime frame room exclusive
    distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree registration.1 at afterRuntime
  rw [←literalEq] at afterRuntime
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.nodes=W.allocation.extra.nodes at nodes
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.locations.size=W.allocation.extra.locations.size at bytes
  rw [←literalEq] at nodes tags bytes
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
    tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
  cases prov : W.pointer.value.provenance with
  | concrete id parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [prov] at binds
    have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
      tagged parentAfter freshAfter nodeCapacity tagBound tagHeld start amount nonzero childBounds
    obtain ⟨child,node,lookup,present,nodeTag,parent,leaf,hidden,old⟩ := S03ReturnChildMetadata.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowConstructorChildActivity.Protected.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    have eqChild : activeChild=child := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using
      And.intro ctor.2.1 (And.intro (ctor.2.2.1.trans bytes) ⟨child,node,lookup,present,nodeTag,leaf,hidden,active⟩)

  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ := GeneralBorrowWildcardConstructorSlot.select output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity (.ReservedFrz false) .None
    have exactTree := GeneralBorrowWildcardConstructorExact.exact output.access.tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter nodeCapacity mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero childBounds
    have present : (GeneralBorrowPositiveWildcardConstructor.result output.access.tree mapping index tracker.global.nextPointerTag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside start amount).nodeAt index = some (WildcardHitZeroConstructor.rootNode tracker.global.nextPointerTag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same output.access.tree.nodes index _
    have lookup := graph.allocator.nodeTags index _ present
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowWildcardRootConstructorActivity.construct output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity start amount nonzero childBounds
    rw [exactTree] at activeLookup active
    have eqChild : activeChild=index := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simp only [prov,CandidateCurrentWindowPointerChecks.extraOf]
    refine ⟨ctor.2.1,ctor.2.2.1.trans bytes,?_⟩
    rw [exactTree]
    exact ⟨index,_,lookup,present,rfl,rfl,rfl,active⟩

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {limits count} (out : Output C limits count)

def parent := CurrentCallSpatialBoolActivation.window out.dst out.physical out.physicalId out.physicalOffset
def machine := CurrentCallSpatialEntry.finalMachine place _ out.physical (CurrentCallSpatialEntry.protectedState C count out.entry out.physical out.fresh out.boolOutput) out.updated
def completion := S05ConcreteProtectedChildCompletion.extend (parent out).precise.completion out.boolChild (parent out).pointer.grant
def pointer := CurrentCallResourceFnEntry.child_pointer (parent out) out.boolOutput.tag out.boolChild

theorem physical_id : out.physical.id=ret.backing.id :=
  out.physicalId.trans (out.dst.id.symm.trans ((congrArg Family.allocation out.returnFamily).trans ret.id))

private theorem allocation_eq : out.physical.entry.allocation=(parent out).allocation := by
  have present : Present (ActualWorld (CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry)) out.physical.id out.physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(out.physical.id,out.physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.physical.live),rfl⟩
  have ids : ((ActualWorld (CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry)).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using out.sourceTracked.allocationIds
  exact CandidateCurrentUniformOwnerWindow.same_id _ ids _ _ _ present (parent out).present

private theorem old_runtime : DuplicatePrefixBorrowContract.RuntimeFacts (parent out).allocation.extra (sourceOutput C).global ∧
    (parent out).allocation.extra.roots.toList.Nodup ∧ (parent out).allocation.extra.nodes.size+1<65536 := by
  let joint:=CurrentCallSpatialJointInstall.context source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry out.allocation out.child out.models
  have distinct : (parent out).allocation.extra.roots.toList.Nodup := by
    rw [←allocation_eq out]
    exact out.sourceTracked.roots _ (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.physical.live))
  by_cases same : out.physical.id=source.backing.id
  · have coverEq:=joint.same_backing out.dst.backingAt
      (CurrentCallSpatialJointInstall.source_member source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry out.allocation out.child out.models)
      (out.physicalId.symm.trans same)
    have treeEq : (parent out).allocation.extra=(sourceOutput C).child.tree := by change out.dst.backing.allocation.extra=_;rw [coverEq];rfl
    rw [treeEq]
    refine ⟨out.sourceRuntime,?_,?_⟩
    · rw [←treeEq];exact distinct
    · have growth:=out.sourceGrowth;have room:=C.sourceRoom;omega
  · have other : ret.backing.id≠source.backing.id := by rw [←physical_id out];exact same
    have coverEq:=joint.same_backing out.dst.backingAt
      (CurrentCallSpatialJointInstall.other_member source C.positive C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry out.allocation out.child out.models ret.backing ret.backingAt other)
      (out.physicalId.symm.trans (physical_id out))
    have treeEq : (parent out).allocation.extra=ret.backing.allocation.extra := by change out.dst.backing.allocation.extra=_;rw [coverEq];rfl
    have present:=ret.backing.live
    simp only [Present,ActualWorld,Array.toList_map] at present
    obtain ⟨row,member,equal⟩:=List.mem_map.mp present
    have rt : DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global :=
      ⟨C.state.formed row member,C.state.coherent row member,C.state.possible row member,C.highwater row member⟩
    have allocEq:row.2.allocation=ret.backing.allocation:=(Prod.mk.inj equal).2
    rw [allocEq] at rt
    have next:=(GeneralBorrowFnEntryRegistrationRuntime.prepare ret.backing.allocation.extra tracker.global C.borrowFrame source.backing.id C.fresh rt).2.2.2.1
    refine ⟨?_,distinct,?_⟩
    · rw [treeEq];exact next
    · rw [treeEq];have room:=C.boolRoom;omega

private theorem witness : Nonempty (CurrentCallResourceFnEntry.BorrowWitness (parent out) out.boolOutput out.boolChild out.physical.offset 1) := out.boolWitness

private theorem source_highwater : ∀row∈(CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry).memory.live.toList,
    GeneralBorrowForestTagHighWater.Below row.2.allocation.extra (sourceOutput C).global.protectedTags (sourceOutput C).global.nextPointerTag := by
  intro row member
  change row∈((before.memory.live.filter (fun row=>row.1!=source.backing.id)).push (source.backing.id,{out.entry with allocation:=out.entry.allocation.setExtra (sourceOutput C).child.tree})).toList at member
  simp only [Array.toList_push,Array.toList_filter,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · have original:=(List.mem_filter.mp old).1
    have runtime : DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global :=
      ⟨C.state.formed row original,C.state.coherent row original,C.state.possible row original,C.highwater row original⟩
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare _ tracker.global C.borrowFrame source.backing.id C.fresh runtime).2.2.2.1.below
  · exact out.sourceRuntime.below

private theorem write_geometry : out.updated.extra.nodes=out.boolOutput.child.tree.nodes ∧
    out.updated.extra.roots=out.boolOutput.child.tree.roots ∧
    out.updated.extra.tagMapping=out.boolOutput.child.tree.tagMapping ∧
    out.updated.extra.locations.size=out.boolOutput.child.tree.locations.size := by
  obtain ⟨w⟩:=witness out
  have result:=(spatial_install_rule ".CurrentCallSpatialBoolActivation.write_runtime")
    frames (RootFrameData.atSpan (argsRoot C count) ⟨601⟩).frame out.physical (parent out) (allocation_eq out)
    (old_runtime out).1 out.sourceTracked (source_highwater out) out.fresh (old_runtime out).2.2
    out.boolOutput out.boolChild out.boolActual out.boolTag out.boolGlobal w
  rw [out.updatedExtra,←out.boolTag]
  exact result.2.2.2.2.2
private theorem write_nodes : out.updated.extra.nodes=out.boolOutput.child.tree.nodes := (write_geometry out).1
private theorem write_roots : out.updated.extra.roots=out.boolOutput.child.tree.roots := (write_geometry out).2.1
private theorem write_tags : out.updated.extra.tagMapping=out.boolOutput.child.tree.tagMapping := (write_geometry out).2.2.1
private theorem write_capacity : out.updated.extra.locations.size=out.boolOutput.child.tree.locations.size := (write_geometry out).2.2.2

theorem live : (machine out).memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,{out.physical.entry with allocation:=out.updated}) :=
  MemoryCopyBridge.live_lookup_replaced _ _ _
theorem present : Present (ActualWorld (machine out)) out.physical.id out.updated := by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(out.physical.id,{out.physical.entry with allocation:=out.updated}),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (live out)),rfl⟩

private theorem issuance :
    SpatialDelegation (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) (parent out).pointer.grant ∧
    SpatialDelegation (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) out.boolChild := by
  let B:=parent out
  obtain ⟨witness⟩ := witness out
  have vacant : B.allocation.extra.nodes.get out.boolChild=none := by
    cases oldAt : B.allocation.extra.nodes.get out.boolChild with
    | none => rfl
    | some old =>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := witness.oldNodes out.boolChild old oldAt
      have same : changed=witness.node := Option.some.inj (changedAt.symm.trans witness.nodeAt)
      have oldTag : old.tag=out.boolOutput.tag := changedTag.symm.trans ((congrArg TreeNode.tag same).trans witness.tag)
      have older:=GeneralBorrowParentTagInvariant.parent_below_fresh B.allocation.extra (sourceOutput C).global (old_runtime out).1 out.boolChild old oldAt
      rw [oldTag,out.boolTag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have parentIssued : SpatialDelegation (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) B.pointer.grant := by
    apply CurrentCallAllocationLicense.spatial B.issued (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.updated
    · exact present out
    · rw [out.boolGlobal];rfl
    · exact out.updatedLength.trans (congrArg Allocation.len (allocation_eq out))
    · exact out.updatedSize.trans (congrArg Allocation.byteSize (allocation_eq out))
    · exact (write_capacity out).trans witness.capacity
    · intro position root found;rw [(write_roots out)];exact witness.oldRoots position root found
    · intro index node found
      obtain ⟨next,nextAt,tag,parent,exposure,permission⟩:=witness.oldNodes index node found
      exact ⟨next,by rw [(write_nodes out)];exact nextAt,tag,parent,exposure,permission⟩
    · intro first second edge
      have different : first≠out.boolChild := by
        intro same
        obtain ⟨node,found⟩ := (B.parents.edgeLive first second edge).1
        rw [same,vacant] at found
        cases found
      change (S05ConcreteProtectedChildCompletion.extend B.precise.completion out.boolChild B.pointer.grant).parents[first.toNat]?=_
      rw [S05ConcreteProtectedChildCompletion.old_parent B.precise.completion out.boolChild B.pointer.grant first different (Array.getElem?_eq_some_iff.mp edge).1]
      exact edge
  have parentIssued' : SpatialDelegation (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) (parent out).pointer.grant := by exact parentIssued
  refine ⟨parentIssued',?_⟩
  have childAt : out.updated.extra.nodes.get out.boolChild=some witness.node := by rw [(write_nodes out)];exact witness.nodeAt
  have shape:=witness.constructor
  cases provenance : B.pointer.value.provenance with
  | concrete supplied tag =>
    rw [provenance] at shape
    obtain ⟨parent,parentAt,_,_⟩ := B.binding
    obtain ⟨next,nextAt,_,_,_,_⟩ := witness.oldNodes B.pointer.grant parent parentAt
    apply SpatialDelegation.concrete parentIssued'
    exact .step (.refl _ next (by rw [(write_nodes out)];exact nextAt)) witness.node childAt shape
  | wildcard =>
    rw [provenance] at shape
    obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path out.updated.extra out.updatedParents.graph out.boolChild witness.node childAt
    have rootEq : root=out.boolChild := by
      cases path with
      | refl => rfl
      | @step predecessor target earlier node found edge =>
        have same : node=witness.node := Option.some.inj (found.symm.trans childAt)
        rw [same,shape] at edge
        cases edge
    subst root
    have edge:=S05ConcreteProtectedChildCompletion.child_edge (parent out).precise.completion out.boolChild (parent out).pointer.grant
    obtain ⟨earlier,originRoot,newRoot,originNode,before,originSlot,newRootAt,originAt,exposed,older,originPath⟩ := out.updatedParents.virtual position out.boolChild rootSlot (parent out).pointer.grant edge
    have same : newRoot=witness.node := Option.some.inj (newRootAt.symm.trans childAt)
    exact SpatialDelegation.wildcard originNode newRoot earlier position originRoot parentIssued' originAt exposed newRootAt (by rw [same];exact shape) older before originSlot rootSlot originPath edge

/-- Original destination parent issuance is retained for use AFTER its actual
child release and whole-frame endCall. No current parent activity is claimed. -/
theorem parent_issued : SpatialDelegation (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) (parent out).pointer.grant := (issuance out).1

theorem issued : SpatialDelegation (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ out.physical.id out.updated (completion out) out.boolChild := (issuance out).2

theorem parent_binding : PointerBinds out.updated (parent out).pointer := by
  obtain ⟨node,found,mapped,binding⟩ := (parent out).binding
  obtain ⟨w⟩:=witness out
  obtain ⟨next,nextAt,tag,_,exposure,_⟩:=w.oldNodes (parent out).pointer.grant node found
  refine ⟨next,by rw [(write_nodes out)];exact nextAt,?_,?_⟩
  · exact out.updatedRuntime.formed.allocator.nodeTags _ _ (by rw [(write_nodes out)];exact nextAt)
  · cases provenance : (parent out).pointer.value.provenance with
    | concrete id parentTag =>
      simp only [provenance] at binding ⊢
      exact ⟨binding.1,binding.2.trans tag.symm⟩
    | wildcard =>
      simp only [provenance] at binding ⊢
      exact exposure.trans binding


def node : TreeNode := (Classical.choice out.boolWitness).node

theorem nodeAt : out.updated.extra.nodes.get out.boolChild=some (node out) := by
  rw [write_nodes out]
  exact (Classical.choice out.boolWitness).nodeAt

theorem nodeTag : (node out).tag=out.boolOutput.tag := (Classical.choice out.boolWitness).tag

theorem facets : (node out).children=#[] ∧ (node out).isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin out.updated.extra out.boolChild .Write out.physical.offset (out.physical.offset+1) := by
  let B:=parent out
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (out.physical.id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent];omega
  obtain ⟨runtime,capacity,child,n,lookup,present,tag,leaf,hidden,active⟩:=selected_facets B (old_runtime out).1
    (sourceOutput C).frame out.fresh rfl (old_runtime out).2.1 (by have h:=(old_runtime out).2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega)
    (by have h:=(old_runtime out).2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega) out.physical.offset 1 rfl rfl (by decide) bounds out.boolOutput out.boolActual
  have ownLookup : out.boolOutput.child.tree.indexOfTag (sourceOutput C).global.nextPointerTag=some out.boolChild := by
    rw [←out.boolTag,←nodeTag out]
    exact (Classical.choice out.boolWitness).runtime.formed.allocator.nodeTags _ _ (Classical.choice out.boolWitness).nodeAt
  have childEq : child=out.boolChild:=Option.some.inj (lookup.symm.trans ownLookup)
  subst child
  have nodeEq : n=node out:=Option.some.inj (present.symm.trans (Classical.choice out.boolWitness).nodeAt)
  subst n
  have childBounds : out.physical.offset.toNat+1≤out.boolOutput.child.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have afterActive:=GeneralBorrowFreshActiveWithinAccess.normal out.boolOutput.child.tree (sourceOutput C).global.nextPointerTag
    (Size.ofBytes out.physical.offset) (Size.ofBytes 1) .Write out.boolOutput.global.protectedTags .VisitChildrenOfAccessed out.boolChild out.physical.offset (out.physical.offset+1)
    runtime.formed.well childBounds (Nat.le_refl _) (Nat.le_refl _) active
  exact ⟨leaf,hidden,by rw [out.updatedExtra];exact afterActive⟩

theorem binding : PointerBinds out.updated (pointer out) := by
  refine ⟨node out,nodeAt out,?_,?_⟩
  · exact out.updatedRuntime.formed.allocator.nodeTags _ _ (nodeAt out)
  · exact ⟨rfl,(nodeTag out).symm⟩

theorem edge : (completion out).parents[out.boolChild.toNat]?=some (some (parent out).pointer.grant) :=
  S05ConcreteProtectedChildCompletion.child_edge _ _ _

theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts out.updated.extra out.boolOutput.global := out.updatedRuntime

theorem parents : ParentInterpretation out.updated.extra (completion out) := out.updatedParents

theorem capacity : out.updated.extra.locations.size=out.physical.entry.allocation.byteSize := by
  obtain ⟨w⟩:=witness out
  exact (write_capacity out).trans (w.capacity.trans ((parent out).issued.capability.treeExtent.trans (congrArg Allocation.byteSize (allocation_eq out).symm)))

theorem roots : out.updated.extra.roots.toList.Nodup := by
  let B:=parent out
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (out.physical.id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent];omega
  rw [write_roots out]
  exact CurrentCallResourceSourceKeyOrigin.roots B (old_runtime out).1 out.sourceTracked (source_highwater out)
    (sourceOutput C).frame out.fresh rfl (old_runtime out).2.1 (by have h:=(old_runtime out).2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega)
    (by have h:=(old_runtime out).2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega) out.physical.offset 1 rfl rfl (by decide) bounds out.boolOutput out.boolActual

theorem short : out.updated.extra.nodes.size<65536 := by
  let B:=parent out
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (out.physical.id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent];omega
  have growth:=CurrentCallResourceBorrowGrowth.operation B (old_runtime out).1 out.sourceTracked (source_highwater out)
    (sourceOutput C).frame out.fresh rfl (old_runtime out).2.1 (by have h:=(old_runtime out).2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega)
    (by have h:=(old_runtime out).2.2;change B.allocation.extra.nodes.size+1<65536 at h;omega) out.physical.offset 1 rfl rfl (by decide) bounds out.boolOutput out.boolActual
  rw [write_nodes out]
  have room:=(old_runtime out).2.2
  change B.allocation.extra.nodes.size+1<65536 at room
  omega

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
  have rights:=out.updatedOwned position valid (by omega) (by omega) (by omega) index node present
  have realized:=CandidateCurrentGrantRuntime.realized _ _ (out.updatedRuntime.possible position valid index node present) ((out.updatedRuntime.formed.profile position valid).present index node present)
  constructor
  · intro below;exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash


private def viewData : Identities :=
  let data := (out.dst.roles (CurrentCallSpatialReturnFrame.returnIndex out.dst) (CurrentCallSpatialReturnFrame.returnOverlap out.dst)).identities
  {data with interpretation:={data.interpretation with
    pointers:=data.interpretation.pointers.push (pointer out)
    loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,some 0,(parent out).loan.depth+1⟩
    precise:=data.interpretation.precise.push (out.physical.id,{(parent out).precise with completion:=completion out})}}

private def view : UniformWindow (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ (viewData out)
    (out.dst.roles (CurrentCallSpatialReturnFrame.returnIndex out.dst) (CurrentCallSpatialReturnFrame.returnOverlap out.dst)).identities.interpretation.loans.size
    out.physical.id out.physical.offset.toNat 1 .ret where
  loan:=⟨(out.dst.roles (CurrentCallSpatialReturnFrame.returnIndex out.dst) (CurrentCallSpatialReturnFrame.returnOverlap out.dst)).identities.interpretation.pointers.size,some 0,(parent out).loan.depth+1⟩
  pointer:=pointer out
  allocation:=out.updated
  precise:={(parent out).precise with completion:=completion out}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=rfl
  present:=present out
  preciseAt:=by simp [viewData]
  binding:=binding out
  issued:=issued out
  parents:=parents out
  window:=window out

/-- A technical backend view of the actual protected child, without a claim
of whole CurrentD or semantic ret-to-mut delegation. -/
theorem current : ∃data owner,∃B : UniformWindow (machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ data owner out.physical.id out.physical.offset.toNat 1 .ret,
    B.pointer=pointer out ∧B.allocation=out.updated ∧B.precise.completion=completion out :=
  ⟨viewData out,_,view out,rfl,rfl,rfl⟩

theorem original_pointer : (parent out).pointer.value=ret.family.value := congrArg Family.value out.returnFamily

theorem original_address : (pointer out).value.offset=C.physical.pointer.offset := by
  change (parent out).pointer.value.offset=C.physical.pointer.offset
  rw [original_pointer out,←C.returnPointer]

end
end DuplicatePrefix.CurrentCallSpatialEntryBoolCurrent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialEntryBoolCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry Bool current dependency {dependency}"
