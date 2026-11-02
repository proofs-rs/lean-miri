import duplicate_prefix.CurrentCallResourceAsMutReturn
import duplicate_prefix.CurrentCallExclusiveWindowFrameSeparate
import duplicate_prefix.CurrentCallResourceReleaseFrame
import duplicate_prefix.CurrentCallResourceSourceActivity
namespace DuplicatePrefix.CurrentCallResourceAsMutBoolFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceAsMutCall CurrentCallResourceAsMutReturn GeneralRangeMapOrigins
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem authority_nodes (before after : BorrowTree) (C : Completion) (flags : ProtectedTags)
    (grant : UniIndex) (location : LocationTree) (nodes : after.nodes=before.nodes)
    (old : Authority before C flags grant location) : Authority after C flags grant location := by
  intro index node present
  rw [nodes] at present
  exact old index node present

private theorem insert_remove (tags : ProtectedTags) (tag : BorTag)
    (different : ∀row∈tags.entries,row.1≠tag) : (tags.insert tag .StrongProtector).remove tag=tags := by
  have unchanged : tags.entries.filter (fun row=>row.1!=tag)=tags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    simpa only [bne_iff_ne] using different row member
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,unchanged]

variable {options limits remaining span before tracker data owner id} {offset len : UInt64}
    (W : UniformWindow before tracker data owner id offset.toNat len.toNat .mut)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (caller : CompilerFrameContext.ActualFrame)
    (base : UInt64) (parentTag : BorTag) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : Miri.MIR.LocalId)<caller.locals.size)
    (seed : Seed options limits remaining span W entry caller base parentTag fresh valid15)

/-- The SAME actual Strong mutable helper and release retain a disjoint Bool
child. Source and Bool technical dictionaries stay independent. -/
theorem same {boolData boolOwner} (boolOffset : UInt64)
    (B : UniformWindow before tracker boolData boolOwner id boolOffset.toNat 1 .ret)
    (allocationEq : B.allocation=W.allocation) (completionEq : B.precise.completion=W.precise.completion)
    (separate : ∀byte,Window id offset.toNat len.toNat byte→Window id boolOffset.toNat 1 byte→False)
    (oldShort : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (boolNode : TreeNode) (boolAt : W.allocation.extra.nodes.get B.pointer.grant=some boolNode)
    (leaf : boolNode.children=#[]) (hidden : boolNode.isExposed=false) (different : B.pointer.grant≠W.pointer.grant)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra B.pointer.grant .Write boolOffset (boolOffset+1)) :
    let tree:=releasedTree W entry caller base parentTag fresh valid15 seed
    let C:=completion W entry caller base parentTag fresh valid15 seed
    let flags:=(postTracker W entry caller base parentTag fresh valid15 seed).global.protectedTags
    OwnedOn (Authority tree C flags B.pointer.grant) boolOffset (boolOffset+1) tree.locations ∧
    (∃next,tree.nodes.get B.pointer.grant=some next ∧ next.tag=boolNode.tag ∧next.parent=boolNode.parent ∧
      next.children=boolNode.children ∧next.isExposed=boolNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin tree B.pointer.grant .Write boolOffset (boolOffset+1) := by
  have bounds : offset.toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
    have h:=seed.bounds
    rw [seed.witness.capacity] at h
    exact h
  have nonzero : len≠0 := by intro zero;have positive:=seed.positive;rw [zero] at positive;exact (UInt64.lt_irrefl _ positive)
  have distinct : W.allocation.extra.roots.toList.Nodup := by rw [←seed.roots];exact seed.distinct
  obtain ⟨output,child,actual,⟨witness⟩,owned,binding,window⟩:=CurrentCallExclusiveWindowFrameSeparate.invoke W B (by omega) rfl allocationEq completionEq separate
    seed.beforeRuntime {} fresh rfl distinct oldShort nodeRoom offset len rfl rfl nonzero bounds
  have outputEq : output=seed.output:=Except.ok.inj (actual.symm.trans seed.operation)
  subst output
  have childEq : child=seed.childIndex:=Option.some.inj ((witness.runtime.formed.allocator.nodeTags _ _ witness.nodeAt).symm.trans (by rw [witness.tag];exact seed.lookup))
  subst child
  have boolFirst:=(B.window (id,boolOffset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have boolFits : boolOffset.toNat+1<2^64 := by have cap:=UInt64.toNat_lt B.allocation.byteSize.bytes;have extent:=B.issued.capability.extent;omega
  have boolEnd : (boolOffset+1).toNat=boolOffset.toNat+1 := by simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt boolFits]
  have naturalOffset : UInt64.ofNat boolOffset.toNat=boolOffset:=UInt64.ofNat_toNat
  have naturalOne : UInt64.ofNat 1=(1 : UInt64):=rfl
  rw [naturalOffset,naturalOne] at owned
  obtain ⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden,nextActivity⟩ :=
    (default_frame_rule ".CurrentCallResourceSourceActivity.fnentry_frame") W seed.beforeRuntime {} fresh rfl distinct oldShort nodeRoom offset len rfl rfl nonzero bounds seed.output seed.operation
      B.pointer.grant boolNode boolAt leaf hidden different boolOffset (boolOffset+1) activity
  obtain ⟨childData,childOwner,current,pointerEq,childAllocation,childCompletion⟩:=CurrentCallResourceAsMutReturn.current W entry caller base parentTag fresh valid15 seed
  have treeEq : current.allocation.extra=seed.output.child.tree := by rw [childAllocation];rfl
  have grantEq : current.pointer.grant=seed.childIndex := by rw [pointerEq];rfl
  obtain ⟨sourceNode,sourceAt,sourceTag,sourceHidden⟩:=seed.hidden
  have sourceCurrent : current.allocation.extra.nodes.get current.pointer.grant=some sourceNode := by rw [treeEq,grantEq];exact sourceAt
  have boolCurrent : current.allocation.extra.nodes.get B.pointer.grant=some next := by rw [treeEq];exact nextAt
  have sourceDifferent : B.pointer.grant≠current.pointer.grant := by
    rw [grantEq]
    intro equal
    have equalNode : next=sourceNode:=Option.some.inj (nextAt.symm.trans (equal.symm ▸ sourceAt))
    have oldFresh:=GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global seed.beforeRuntime B.pointer.grant boolNode boolAt
    have eq : boolNode.tag=tracker.global.nextPointerTag:=nextTag.symm.trans ((congrArg TreeNode.tag equalNode).trans (sourceTag.trans seed.tag))
    rw [eq] at oldFresh
    exact UInt64.lt_irrefl _ oldFresh
  have sumFits : offset.toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt seed.bounds (UInt64.toNat_lt seed.output.child.tree.locations.size.bytes)
  have noWrap : (offset+len).toNat=offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]
  have positive : offset.toNat<(offset+len).toNat := by have pos:=UInt64.lt_iff_toNat_lt.mp seed.positive;rw [noWrap];simp only [UInt64.toNat_zero] at pos;omega
  have disjoint : (offset+len).toNat≤boolOffset.toNat ∨ (boolOffset+1).toNat≤offset.toNat := by
    by_cases left : offset.toNat+len.toNat≤boolOffset.toNat
    · exact .inl (by omega)
    · by_cases right : (boolOffset+1).toNat≤offset.toNat
      · exact .inr right
      · apply False.elim
        have point : Window id offset.toNat len.toNat (id,boolOffset.toNat) := ⟨rfl,by omega,by omega⟩
        exact separate _ point ⟨rfl,Nat.le_refl _,by omega⟩
  let predicate:=Authority seed.output.child.tree (completion W entry caller base parentTag fresh valid15 seed) seed.output.global.protectedTags B.pointer.grant
  have ownedCurrent : OwnedOn predicate boolOffset (boolOffset+1) current.allocation.extra.locations := by rw [treeEq];exact owned
  have preserved:=CurrentCallResourceReleaseFrame.preserve current rfl (by rw [treeEq];exact seed.witness.runtime)
    ⟨id,seed.output.tag,by rw [pointerEq];rfl⟩ (by rw [treeEq];exact seed.distinct) (by rw [treeEq];exact seed.short)
    sourceNode sourceCurrent sourceHidden offset len rfl rfl positive noWrap (by rw [treeEq,grantEq];exact seed.activity)
    boolOffset (boolOffset+1) (by omega) disjoint predicate ownedCurrent B.pointer.grant next boolCurrent
    (nextChildren.trans leaf) (nextHidden.trans hidden) sourceDifferent (by rw [treeEq];exact nextActivity)
  rw [treeEq,sourceTag] at preserved
  have release:=(CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.1
  have nodes:=congrArg BorrowTree.nodes release
  refine ⟨?_,⟨next,?_,nextTag,nextParent,nextChildren,nextHidden⟩,preserved.2⟩
  · intro cursor valid pos lower upper
    have authority:=preserved.1 cursor valid pos lower upper
    have sameAuthority : Authority (releasedTree W entry caller base parentTag fresh valid15 seed)
        (completion W entry caller base parentTag fresh valid15 seed) seed.output.global.protectedTags B.pointer.grant
        (releasedTree W entry caller base parentTag fresh valid15 seed).locations.entries[cursor].data := by
      exact authority_nodes _ _ _ _ _ _ nodes authority
    exact (default_frame_rule ".CurrentCallResourceAsMutReturn.authority_weaken") _ _ _ _ _ _
      (GeneralBorrowRelease.end_call_weakens seed.output.global seed.output.frame) sameAuthority
  · change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.nodes.get _=_
    rw [nodes];exact nextAt
variable (result : Returned W entry caller base parentTag fresh valid15 seed)

theorem present : Present (ActualWorld result.machine) id (W.allocation.setExtra (releasedTree W entry caller base parentTag fresh valid15 seed)) := by
  simp only [Present,ActualWorld,Array.toList_map]
  apply List.mem_map.mpr
  refine ⟨(id,{entry with allocation:=entry.allocation.setExtra (releasedTree W entry caller base parentTag fresh valid15 seed)}),
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some result.sourceLive),?_⟩
  rw [seed.allocationEq]

theorem metadata (index : UniIndex) (node : TreeNode) (old : W.allocation.extra.nodes.get index=some node) :
    ∃next,(releasedTree W entry caller base parentTag fresh valid15 seed).nodes.get index=some next ∧
      next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission := by
  obtain ⟨next,nextAt,tag,parent,exposure,permission⟩:=seed.witness.oldNodes index node old
  refine ⟨next,?_,tag,parent,exposure,permission⟩
  change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.nodes.get index=some next
  rw [(CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.1]
  exact nextAt

private theorem vacant : W.allocation.extra.nodes.get seed.childIndex=none := by
  cases old : W.allocation.extra.nodes.get seed.childIndex with
  | none=>rfl
  | some node=>
    obtain ⟨changed,changedAt,tag,_,_,_⟩:=seed.witness.oldNodes seed.childIndex node old
    have one:=seed.witness.runtime.formed.allocator.nodeTags seed.childIndex changed changedAt
    obtain ⟨actual,atActual,tagActual,_⟩:=seed.hidden
    have equal : changed=actual:=Option.some.inj (changedAt.symm.trans atActual)
    have eq : node.tag=tracker.global.nextPointerTag:=tag.symm.trans ((congrArg TreeNode.tag equal).trans (tagActual.trans seed.tag))
    have below:=GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global seed.beforeRuntime seed.childIndex node old
    rw [eq] at below
    exact False.elim (UInt64.lt_irrefl _ below)

theorem old_edge (child parent : UniIndex) (edge : W.precise.completion.parents[child.toNat]?=some (some parent)) :
    (completion W entry caller base parentTag fresh valid15 seed).parents[child.toNat]?=some (some parent) := by
  have different : child≠seed.childIndex := by
    intro same
    obtain ⟨node,found⟩:=(W.parents.edgeLive child parent edge).1
    rw [same,vacant W entry caller base parentTag fresh valid15 seed] at found
    cases found
  exact (S05ConcreteProtectedChildCompletion.old_parent W.precise.completion seed.childIndex W.pointer.grant child different
    (Array.getElem?_eq_some_iff.mp edge).1).trans edge

/-- Transport any original destination license, separately from current raw
parent authority, through the actual constructor/release/endCall/pop. -/
theorem license {grant : UniIndex} (old : SpatialDelegation before tracker id W.allocation W.precise.completion grant) :
    SpatialDelegation result.machine (postTracker W entry caller base parentTag fresh valid15 seed) id
      (W.allocation.setExtra (releasedTree W entry caller base parentTag fresh valid15 seed))
      (completion W entry caller base parentTag fresh valid15 seed) grant := by
  apply CurrentCallAllocationLicense.spatial old result.machine (postTracker W entry caller base parentTag fresh valid15 seed) _
    (present W entry caller base parentTag fresh valid15 seed result)
  · rw [postTracker,seed.global];rfl
  · rfl
  · rfl
  · exact (CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.2.2.2.1 |>.trans seed.witness.capacity
  · intro position root oldRoot
    change (releasedTree W entry caller base parentTag fresh valid15 seed).roots[position]?=some root
    rw [releasedTree,(CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.1]
    exact seed.witness.oldRoots position root oldRoot
  · exact metadata W entry caller base parentTag fresh valid15 seed
  · exact old_edge W entry caller base parentTag fresh valid15 seed

theorem old_binding (pointer : PointerInstance) (old : PointerBinds W.allocation pointer) :
    PointerBinds (W.allocation.setExtra (releasedTree W entry caller base parentTag fresh valid15 seed)) pointer := by
  obtain ⟨node,found,mapped,provenance⟩:=old
  obtain ⟨next,nextAt,tag,_,exposure,_⟩:=metadata W entry caller base parentTag fresh valid15 seed pointer.grant node found
  refine ⟨next,nextAt,?_,?_⟩
  · exact (runtime_end_call W entry caller base parentTag fresh valid15 seed).formed.allocator.nodeTags _ _ nextAt
  · cases prov : pointer.value.provenance with
    | concrete supplied parentTag=>
      simp only [prov] at provenance ⊢
      exact ⟨provenance.1,provenance.2.trans tag.symm⟩
    | wildcard=>
      simp only [prov] at provenance ⊢
      exact exposure.trans provenance

/-- The Bool family and owner slots remain fixed in the actual returned world;
only its completion dictionary gains the real helper edge. -/
theorem current {boolData boolOwner} (boolOffset : UInt64)
    (B : UniformWindow before tracker boolData boolOwner id boolOffset.toNat 1 .ret)
    (allocationEq : B.allocation=W.allocation) (completionEq : B.precise.completion=W.precise.completion)
    (separate : ∀byte,Window id offset.toNat len.toNat byte→Window id boolOffset.toNat 1 byte→False)
    (oldShort : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (boolNode : TreeNode) (boolAt : W.allocation.extra.nodes.get B.pointer.grant=some boolNode)
    (leaf : boolNode.children=#[]) (hidden : boolNode.isExposed=false) (different : B.pointer.grant≠W.pointer.grant)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra B.pointer.grant .Write boolOffset (boolOffset+1)) :
    ∃nextData,∃next : UniformWindow result.machine (postTracker W entry caller base parentTag fresh valid15 seed)
      nextData boolOwner id boolOffset.toNat 1 .ret,
      next.pointer=B.pointer ∧next.loan=B.loan ∧next.allocation=W.allocation.setExtra (releasedTree W entry caller base parentTag fresh valid15 seed) ∧
      next.precise.completion=completion W entry caller base parentTag fresh valid15 seed := by
  obtain ⟨owned,facets,active⟩:=same W entry caller base parentTag fresh valid15 seed boolOffset B allocationEq completionEq separate
    oldShort nodeRoom boolNode boolAt leaf hidden different activity
  let tree:=releasedTree W entry caller base parentTag fresh valid15 seed
  let Cnew:=completion W entry caller base parentTag fresh valid15 seed
  let nextTracker:=postTracker W entry caller base parentTag fresh valid15 seed
  let nextData : Identities:={boolData with interpretation:={boolData.interpretation with
    precise:=boolData.interpretation.precise.push (id,{B.precise with completion:=Cnew})}}
  have oldIssued : SpatialDelegation before tracker id W.allocation W.precise.completion B.pointer.grant := by
    rw [←allocationEq,←completionEq];exact B.issued
  have issuedB:=license W entry caller base parentTag fresh valid15 seed result oldIssued
  have bindingB:=old_binding W entry caller base parentTag fresh valid15 seed B.pointer (by rw [←allocationEq];exact B.binding)
  have window : ∀byte,Window id boolOffset.toNat 1 byte→byte.2<(W.allocation.setExtra tree).len ∧
      CandidateCurrentGrantResources.Embeds (W.allocation.setExtra tree) nextTracker.global.protectedTags Cnew B.pointer.grant byte.2 .exclusive := by
    have first:=(B.window (id,boolOffset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    have endFits : boolOffset.toNat+1<2^64 := by have cap:=UInt64.toNat_lt B.allocation.byteSize.bytes;have extent:=B.issued.capability.extent;omega
    have endEq : (boolOffset+1).toNat=boolOffset.toNat+1:=by simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endFits]
    intro byte inside
    refine ⟨?_,?_⟩
    · have bound:=(B.window byte inside).1
      change byte.2<W.allocation.len
      rw [←allocationEq];exact bound
    · intro segment member lower upper index node present
      obtain ⟨position,valid,sameSegment⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      subst segment
      change (releasedTree W entry caller base parentTag fresh valid15 seed).locations.entries[position].range.start.toNat≤byte.2 at lower
      change byte.2<(releasedTree W entry caller base parentTag fresh valid15 seed).locations.entries[position].range.stop.toNat at upper
      have interval:=inside.2
      have rights:=owned position valid (by omega) (by omega) (by omega) index node present
      have runtime:=runtime_end_call W entry caller base parentTag fresh valid15 seed
      have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node present)
        ((runtime.formed.profile position valid).present index node present)
      constructor
      · intro below
        exact (default_frame_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
      · intro clash
        apply Classical.byContradiction
        intro outside
        exact (default_frame_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash
  let next : UniformWindow result.machine nextTracker nextData boolOwner id boolOffset.toNat 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=W.allocation.setExtra tree,precise:={B.precise with completion:=Cnew}
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId
    present:=present W entry caller base parentTag fresh valid15 seed result
    preciseAt:=by simp [nextData]
    binding:=bindingB,issued:=issuedB
    parents:=(CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.2.2.1
    window:=window}
  exact ⟨nextData,next,rfl,rfl,rfl,rfl⟩

theorem flags : (postTracker W entry caller base parentTag fresh valid15 seed).global.protectedTags=tracker.global.protectedTags := by
  change (seed.output.global.endCall seed.output.frame).protectedTags=tracker.global.protectedTags
  rw [seed.global,seed.frameEq]
  change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).remove tracker.global.nextPointerTag=tracker.global.protectedTags
  apply insert_remove
  intro row member equal
  have below:=seed.beforeRuntime.below.protectors row member
  rw [equal] at below
  omega

theorem different_present {boolId : AllocId} (different : boolId≠id)
    (allocation : Allocation Provenance BorrowTree) (old : Present (ActualWorld before) boolId allocation) :
    Present (ActualWorld result.machine) boolId allocation := by
  simp only [Present,ActualWorld,Array.toList_map] at old ⊢
  obtain ⟨row,member,equal⟩:=List.mem_map.mp old
  refine List.mem_map.mpr ⟨row,?_,equal⟩
  rw [result.memory]
  change row∈((before.memory.live.filter (fun row=>row.1!=id)).push _).toList
  simp only [Array.toList_push,Array.toList_filter,List.mem_append,List.mem_singleton]
  apply Or.inl
  apply List.mem_filter.mpr
  exact ⟨member,by have rowId:=congrArg Prod.fst equal;simp only at rowId;simpa only [rowId,bne_iff_ne] using different⟩

theorem different_license {boolId : AllocId} {allocation : Allocation Provenance BorrowTree} {C : Completion} {grant : UniIndex}
    (different : boolId≠id) (old : SpatialDelegation before tracker boolId allocation C grant) :
    SpatialDelegation result.machine (postTracker W entry caller base parentTag fresh valid15 seed) boolId allocation C grant := by
  apply CurrentCallAllocationLicense.spatial old result.machine (postTracker W entry caller base parentTag fresh valid15 seed) allocation
    (different_present W entry caller base parentTag fresh valid15 seed result different allocation old.capability.live)
  · rw [postTracker,seed.global];rfl
  · rfl
  · rfl
  · rfl
  · intro position root found;exact found
  · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
  · intro root origin edge;exact edge

theorem different_runtime (tree : BorrowTree) (old : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (postTracker W entry caller base parentTag fresh valid15 seed).global := by
  have registered:=(GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} id fresh old).2.2.2.1
  rw [←seed.global] at registered
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame tree seed.output.frame := by
    intro row member index node present sameTag
    rw [seed.frameOwned] at member
    have sameRow : row=(id,seed.output.tag):=List.mem_singleton.mp member
    subst row
    have below:=GeneralBorrowParentTagInvariant.parent_below_fresh tree tracker.global old index node present
    rw [sameTag,seed.tag] at below
    exact False.elim (UInt64.lt_irrefl _ below)
  exact S05CompletedChildReanchor.runtime_end_call tree seed.output.global seed.output.frame registered hiddenFrame

/-- A different live Bool backing is literally retained by both source heap
updates and helper pop. Its original family/loan/precise dictionary is reused. -/
theorem different {boolData boolOwner boolId boolOffset}
    (B : UniformWindow before tracker boolData boolOwner boolId boolOffset 1 .ret)
    (different : boolId≠id) :
    ∃next : UniformWindow result.machine (postTracker W entry caller base parentTag fresh valid15 seed) boolData boolOwner boolId boolOffset 1 .ret,
      next.pointer=B.pointer ∧next.loan=B.loan ∧next.allocation=B.allocation ∧next.precise=B.precise := by
  let next : UniformWindow result.machine (postTracker W entry caller base parentTag fresh valid15 seed) boolData boolOwner boolId boolOffset 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=B.allocation,precise:=B.precise
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId,preciseAt:=B.preciseAt
    present:=different_present W entry caller base parentTag fresh valid15 seed result different B.allocation B.present
    binding:=B.binding,issued:=different_license W entry caller base parentTag fresh valid15 seed result different B.issued
    parents:=B.parents,window:=by rw [flags W entry caller base parentTag fresh valid15 seed];exact B.window}
  exact ⟨next,rfl,rfl,rfl,rfl⟩

theorem nodes : (releasedTree W entry caller base parentTag fresh valid15 seed).nodes=seed.output.child.tree.nodes := by
  have eq:=congrArg BorrowTree.nodes (CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.1
  exact eq

theorem roots : (releasedTree W entry caller base parentTag fresh valid15 seed).roots.toList.Nodup := by
  have eq:=congrArg BorrowTree.roots (CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.1
  change (releasedTree W entry caller base parentTag fresh valid15 seed).roots=seed.output.child.tree.roots at eq
  rw [eq];exact seed.distinct

theorem short : (releasedTree W entry caller base parentTag fresh valid15 seed).nodes.size<65536 := by
  rw [nodes W entry caller base parentTag fresh valid15 seed];exact seed.short

theorem capacity : (releasedTree W entry caller base parentTag fresh valid15 seed).locations.size=W.allocation.extra.locations.size :=
  (CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.2.2.2.1 |>.trans seed.witness.capacity

theorem parents : ParentInterpretation (releasedTree W entry caller base parentTag fresh valid15 seed)
    (completion W entry caller base parentTag fresh valid15 seed) :=
  (CurrentCallResourceAsMutReturn.release W entry caller base parentTag fresh valid15 seed).2.2.2.1

end
end DuplicatePrefix.CurrentCallResourceAsMutBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAsMutBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual mutable helper Bool frame dependency {dependency}"
