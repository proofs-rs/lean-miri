import duplicate_prefix.CurrentCallResourceAsMutInvoke
import duplicate_prefix.CurrentCallDefaultMutableDisjoint
import duplicate_prefix.CurrentCallResourceSourceActivity
import duplicate_prefix.CurrentCallExclusiveWindowFrame
namespace DuplicatePrefix.CurrentCallResourceDefaultBoolFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceAsMutInvoke GeneralRangeMapOrigins GeneralBorrowFnEntryRegistration
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- Both phases are the SAME actual Default mutable Read/constructor named by
DefaultStage. The Bool child remains on its original interval and grant. -/
theorem same {before tracker qData qOwner id offset length boolData boolOwner}
    (Q : UniformWindow before tracker qData qOwner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : Q.allocation.extra.roots.toList.Nodup) (short : Q.allocation.extra.nodes.size<65536)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (stage : DefaultStage Q tag room start amount)
    (boolOffset : UInt64) (B : UniformWindow before tracker boolData boolOwner id boolOffset.toNat 1 .ret)
    (allocationEq : B.allocation=Q.allocation) (completionEq : B.precise.completion=Q.precise.completion)
    (separate : ∀byte,Window id offset length byte→Window id boolOffset.toNat 1 byte→False)
    (boolNode : TreeNode) (boolAt : Q.allocation.extra.nodes.get B.pointer.grant=some boolNode)
    (leaf : boolNode.children=#[]) (hidden : boolNode.isExposed=false) (different : B.pointer.grant≠Q.pointer.grant)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra B.pointer.grant .Write boolOffset (boolOffset+1)) :
    let tree:=(GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
    OwnedOn (Authority tree (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.childIndex Q.pointer.grant)
      (advanced tracker.global room).protectedTags B.pointer.grant) boolOffset (boolOffset+1) tree.locations ∧
    (∃next,tree.nodes.get B.pointer.grant=some next ∧next.tag=boolNode.tag ∧next.parent=boolNode.parent ∧
      next.children=boolNode.children ∧next.isExposed=boolNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin tree B.pointer.grant .Write boolOffset (boolOffset+1) := by
  obtain ⟨P⟩:=CurrentCallResourceDefaultShared.prepare Q runtime tag concrete room distinct short start amount startEq amountEq bounds
  let read:=GeneralBorrowRawSharedExpression.read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have boolFirst:=(B.window (id,boolOffset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have boolFits : boolOffset.toNat+1<2^64 := by have cap:=UInt64.toNat_lt B.allocation.byteSize.bytes;have extent:=B.issued.capability.extent;omega
  have boolEnd : (boolOffset+1).toNat=boolOffset.toNat+1 := by simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt boolFits]
  have initialOwned:=(default_frame_rule ".CurrentCallExclusiveWindowFrame.window_owned") B rfl
    (by rw [allocationEq];exact runtime) boolOffset (boolOffset+1) (Nat.le_refl _) (by omega)
  rw [allocationEq,completionEq] at initialOwned
  have noWrap : (start+amount).toNat=start.toNat+amount.toNat := by
    have fits:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt Q.allocation.extra.locations.size.bytes)
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have disjoint : ∀point : UInt64,boolOffset.toNat≤point.toNat→point.toNat<(boolOffset+1).toNat→point.toNat<start.toNat ∨ (start+amount).toNat≤point.toNat := by
    intro point lower upper
    by_cases early : point.toNat<start.toNat
    · exact .inl early
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro overlap
      exact separate (id,point.toNat) ⟨rfl,by omega,by omega⟩ ⟨rfl,by omega,by omega⟩
  have readOwned:=GeneralBorrowRangeOutsideOwned.owned (Authority Q.allocation.extra Q.precise.completion tracker.global.protectedTags B.pointer.grant)
    Q.allocation.extra (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    runtime.formed.well bounds boolOffset (boolOffset+1) disjoint initialOwned
  have afterOwned : OwnedOn (Authority read.tree Q.precise.completion (advanced tracker.global room).protectedTags B.pointer.grant)
      boolOffset (boolOffset+1) read.tree.locations := by
    intro position valid positive lower upper index node present
    exact readOwned position valid positive lower upper index node (by rw [←P.nodes];exact present)
  obtain ⟨parent,parentAt,mapped,binding⟩:=Q.binding
  rw [concrete] at binding
  have tagged : Q.allocation.extra.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact mapped
  have normals:=(default_frame_rule ".CurrentCallResourceSourceActivity.window_normals") Q P.geometry runtime rfl start amount startEq amountEq bounds
  have readActive:=CurrentCallRootActivity.concrete_of_normal Q.allocation.extra tracker.global runtime tag Q.pointer.grant B.pointer.grant parent parentAt
    start amount bounds normals tagged boolNode boolAt leaf hidden different boolOffset (boolOffset+1) activity .Read .VisitChildrenOfAccessed
  have parentAfter : read.tree.nodes.get Q.pointer.grant=some parent := by rw [P.nodes];exact parentAt
  have boolAfter : read.tree.nodes.get B.pointer.grant=some boolNode := by rw [P.nodes];exact boolAt
  have taggedAfter : read.tree.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have fresh:=(GeneralBorrowFnEntryRegistrationRuntime.prepare Q.allocation.extra tracker.global {} id room runtime).2.2.2.2.2
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  have roomAfter : read.tree.nodes.size+1≤4294967295 := by rw [P.nodes];exact nodeRoom
  have boundsAfter : start.toNat+amount.toNat≤read.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<(advanced tracker.global room).nextPointerTag.value.toNat := by
    have next:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,_,_,_,child,lookup,owned⟩:=CurrentCallDefaultMutableDisjoint.disjoint read.tree (advanced tracker.global room) Q.precise.completion P.runtime P.parents
    tag tracker.global.nextPointerTag Q.pointer.grant B.pointer.grant parent boolNode taggedAfter parentAfter boolAfter freshAfter roomAfter tagBound stage.unheld
    start amount boolOffset (boolOffset+1) nonzero boundsAfter disjoint afterOwned
  have childEq : child=stage.childIndex:=Option.some.inj (lookup.symm.trans stage.lookup)
  subst child
  have facets:=CurrentCallDefaultMutableDisjoint.old_facets read.tree (advanced tracker.global room) P.runtime tag tracker.global.nextPointerTag
    Q.pointer.grant B.pointer.grant parent boolNode taggedAfter parentAfter boolAfter different freshAfter roomAfter start amount nonzero boundsAfter
    .Write boolOffset (boolOffset+1) readActive
  exact ⟨owned,facets.1,facets.2⟩
variable {before tracker qData qOwner id offset length}
    (Q : UniformWindow before tracker qData qOwner id offset length .mut)
    (tag : BorTag) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (stage : DefaultStage Q tag room start amount)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (allocationEq : Q.allocation=entry.allocation)

include allocationEq in
theorem present : Present (ActualWorld (defaultMachine before tracker room id entry (defaultTree Q tag start amount)))
    id (Q.allocation.setExtra (defaultTree Q tag start amount)) := by
  simp only [Present,ActualWorld,Array.toList_map]
  have live : (defaultMachine before tracker room id entry (defaultTree Q tag start amount)).memory.live.find? (fun row=>row.1==id)=
      some (id,{entry with allocation:=entry.allocation.setExtra (defaultTree Q tag start amount)}) := MemoryCopyBridge.live_lookup_replaced before.memory id _
  refine List.mem_map.mpr ⟨(id,{entry with allocation:=entry.allocation.setExtra (defaultTree Q tag start amount)}),
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),?_⟩
  rw [allocationEq]

private theorem read_nodes : (GeneralBorrowRawDefaultExpression.read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.nodes=Q.allocation.extra.nodes := by
  have frame:=GeneralBorrowFreshReadFrame.frame Q.allocation.extra (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  have eq:=congrArg BorrowTree.nodes frame
  exact eq

theorem old_edge (child parent : UniIndex) (edge : Q.precise.completion.parents[child.toNat]?=some (some parent)) :
    (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.childIndex Q.pointer.grant).parents[child.toNat]?=some (some parent) := by
  have vacant:=stage.leaf.vacant
  rw [read_nodes Q tag start amount] at vacant
  have different : child≠stage.childIndex := by
    intro equal
    obtain ⟨node,found⟩:=(Q.parents.edgeLive child parent edge).1
    rw [equal,vacant] at found
    cases found
  exact (S05ConcreteProtectedChildCompletion.old_parent Q.precise.completion stage.childIndex Q.pointer.grant child different
    (Array.getElem?_eq_some_iff.mp edge).1).trans edge

include allocationEq in
/-- Original destination issuance is transported to the exact actual Default
installation. It is not an active parent-content claim. -/
theorem license {grant : UniIndex} (old : SpatialDelegation before tracker id Q.allocation Q.precise.completion grant) :
    SpatialDelegation (defaultMachine before tracker room id entry (defaultTree Q tag start amount)) (defaultTracker tracker room) id
      (Q.allocation.setExtra (defaultTree Q tag start amount))
      (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.childIndex Q.pointer.grant) grant := by
  apply CurrentCallAllocationLicense.spatial old _ (defaultTracker tracker room) _ (present Q tag room start amount entry allocationEq)
  · rfl
  · rfl
  · rfl
  · exact stage.capacity
  · intro position root found
    change (defaultTree Q tag start amount).roots[position]?=some root
    rw [stage.roots];exact found
  · exact stage.oldNodes
  · exact old_edge Q tag room start amount stage

include stage in
theorem old_binding (pointer : PointerInstance) (old : PointerBinds Q.allocation pointer) :
    PointerBinds (Q.allocation.setExtra (defaultTree Q tag start amount)) pointer := by
  obtain ⟨node,found,mapped,binding⟩:=old
  obtain ⟨next,nextAt,tagEq,_,exposure,_⟩:=stage.oldNodes pointer.grant node found
  refine ⟨next,nextAt,stage.runtime.formed.allocator.nodeTags _ _ nextAt,?_⟩
  cases prov : pointer.value.provenance with
  | concrete supplied parentTag=>simp only [prov] at binding ⊢;exact ⟨binding.1,binding.2.trans tagEq.symm⟩
  | wildcard=>simp only [prov] at binding ⊢;exact exposure.trans binding

theorem current {before tracker qData qOwner id offset length boolData boolOwner}
    (Q : UniformWindow before tracker qData qOwner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : Q.allocation.extra.roots.toList.Nodup) (short : Q.allocation.extra.nodes.size<65536)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (stage : DefaultStage Q tag room start amount)
    (boolOffset : UInt64) (B : UniformWindow before tracker boolData boolOwner id boolOffset.toNat 1 .ret)
    (allocationEq : B.allocation=Q.allocation) (completionEq : B.precise.completion=Q.precise.completion)
    (separate : ∀byte,Window id offset length byte→Window id boolOffset.toNat 1 byte→False)
    (boolNode : TreeNode) (boolAt : Q.allocation.extra.nodes.get B.pointer.grant=some boolNode)
    (leaf : boolNode.children=#[]) (hidden : boolNode.isExposed=false) (different : B.pointer.grant≠Q.pointer.grant)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra B.pointer.grant .Write boolOffset (boolOffset+1))
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : Q.allocation=entry.allocation) :
    ∃nextData,∃next : UniformWindow (defaultMachine before tracker room id entry (defaultTree Q tag start amount))
      (defaultTracker tracker room) nextData boolOwner id boolOffset.toNat 1 .ret,
      next.pointer=B.pointer ∧next.loan=B.loan ∧next.allocation=Q.allocation.setExtra (defaultTree Q tag start amount) ∧
      next.precise.completion=S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.childIndex Q.pointer.grant := by
  obtain ⟨owned,facets,active⟩:=same Q runtime tag concrete room distinct short nodeRoom start amount startEq amountEq nonzero bounds
    stage boolOffset B allocationEq completionEq separate boolNode boolAt leaf hidden different activity
  let tree:=defaultTree Q tag start amount
  let Cnew:=S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.childIndex Q.pointer.grant
  let nextData : Identities:={boolData with interpretation:={boolData.interpretation with
    precise:=boolData.interpretation.precise.push (id,{B.precise with completion:=Cnew})}}
  have oldIssued : SpatialDelegation before tracker id Q.allocation Q.precise.completion B.pointer.grant := by
    rw [←allocationEq,←completionEq];exact B.issued
  have issuedB:=license Q tag room start amount stage entry entryEq oldIssued
  have bindingB:=old_binding Q tag room start amount stage B.pointer (by rw [←allocationEq];exact B.binding)
  have window : ∀byte,Window id boolOffset.toNat 1 byte→byte.2<(Q.allocation.setExtra tree).len ∧
      CandidateCurrentGrantResources.Embeds (Q.allocation.setExtra tree) (defaultTracker tracker room).global.protectedTags Cnew B.pointer.grant byte.2 .exclusive := by
    have first:=(B.window (id,boolOffset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    have endFits : boolOffset.toNat+1<2^64 := by have cap:=UInt64.toNat_lt B.allocation.byteSize.bytes;have extent:=B.issued.capability.extent;omega
    have endEq : (boolOffset+1).toNat=boolOffset.toNat+1:=by simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endFits]
    intro byte inside
    refine ⟨?_,?_⟩
    · have bound:=(B.window byte inside).1
      change byte.2<Q.allocation.len
      rw [←allocationEq];exact bound
    · intro segment member lower upper index node present
      obtain ⟨position,valid,sameSegment⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      subst segment
      change tree.locations.entries[position].range.start.toNat≤byte.2 at lower
      change byte.2<tree.locations.entries[position].range.stop.toNat at upper
      have interval:=inside.2
      change OwnedOn (Authority tree Cnew (defaultTracker tracker room).global.protectedTags B.pointer.grant) boolOffset (boolOffset+1) tree.locations at owned
      have rights:=owned position valid (by omega) (by omega) (by omega) index node present
      have realized:=CandidateCurrentGrantRuntime.realized _ _ (stage.runtime.possible position valid index node present)
        ((stage.runtime.formed.profile position valid).present index node present)
      constructor
      · intro below
        exact (default_frame_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
      · intro clash
        apply Classical.byContradiction
        intro outside
        exact (default_frame_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash
  let next : UniformWindow (defaultMachine before tracker room id entry tree) (defaultTracker tracker room) nextData boolOwner id boolOffset.toNat 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=Q.allocation.setExtra tree,precise:={B.precise with completion:=Cnew}
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId
    present:=present Q tag room start amount entry entryEq
    preciseAt:=by simp [nextData]
    binding:=bindingB,issued:=issuedB,parents:=stage.parents,window:=window}
  exact ⟨nextData,next,rfl,rfl,rfl,rfl⟩

theorem different_present {boolId : AllocId} (different : boolId≠id)
    (allocation : Allocation Provenance BorrowTree) (old : Present (ActualWorld before) boolId allocation) :
    Present (ActualWorld (defaultMachine before tracker room id entry (defaultTree Q tag start amount))) boolId allocation := by
  simp only [Present,ActualWorld,Array.toList_map] at old ⊢
  obtain ⟨row,member,equal⟩:=List.mem_map.mp old
  refine List.mem_map.mpr ⟨row,?_,equal⟩
  change row∈((before.memory.live.filter (fun row=>row.1!=id)).push _).toList
  simp only [Array.toList_push,Array.toList_filter,List.mem_append,List.mem_singleton]
  apply Or.inl
  apply List.mem_filter.mpr
  exact ⟨member,by have rowId:=congrArg Prod.fst equal;simp only at rowId;simpa only [rowId,bne_iff_ne] using different⟩

theorem different_license {boolId : AllocId} {allocation : Allocation Provenance BorrowTree} {C : Completion} {grant : UniIndex}
    (different : boolId≠id) (old : SpatialDelegation before tracker boolId allocation C grant) :
    SpatialDelegation (defaultMachine before tracker room id entry (defaultTree Q tag start amount)) (defaultTracker tracker room) boolId allocation C grant := by
  apply CurrentCallAllocationLicense.spatial old _ (defaultTracker tracker room) allocation
    (different_present Q tag room start amount entry different allocation old.capability.live)
  · rfl
  · rfl
  · rfl
  · rfl
  · intro position root found;exact found
  · intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩
  · intro root origin edge;exact edge

theorem different {boolData boolOwner boolId boolOffset}
    (B : UniformWindow before tracker boolData boolOwner boolId boolOffset 1 .ret) (different : boolId≠id) :
    ∃next : UniformWindow (defaultMachine before tracker room id entry (defaultTree Q tag start amount)) (defaultTracker tracker room)
      boolData boolOwner boolId boolOffset 1 .ret,
      next.pointer=B.pointer ∧next.loan=B.loan ∧next.allocation=B.allocation ∧next.precise=B.precise := by
  let next : UniformWindow (defaultMachine before tracker room id entry (defaultTree Q tag start amount)) (defaultTracker tracker room)
      boolData boolOwner boolId boolOffset 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=B.allocation,precise:=B.precise
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId,preciseAt:=B.preciseAt
    present:=different_present Q tag room start amount entry different B.allocation B.present
    binding:=B.binding,issued:=different_license Q tag room start amount entry different B.issued
    parents:=B.parents,window:=B.window}
  exact ⟨next,rfl,rfl,rfl,rfl⟩

theorem advance_runtime (tree : BorrowTree) (old : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (defaultTracker tracker room).global := by
  have next:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
  refine ⟨old.formed,old.coherent,old.possible,⟨?_,?_⟩⟩
  · intro row member
    have before:=old.below.mapping row member
    change row.1.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  · intro row member
    have before:=old.below.protectors row member
    change row.1.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega

end
end DuplicatePrefix.CurrentCallResourceDefaultBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceDefaultBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Default Bool frame dependency {dependency}"
