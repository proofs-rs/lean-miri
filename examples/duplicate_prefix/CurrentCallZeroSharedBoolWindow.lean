import duplicate_prefix.CurrentCallZeroSharedBoolFrame
import duplicate_prefix.CurrentCallResourceCopyInstall
import duplicate_prefix.CurrentCallExclusiveWindowFrame
namespace DuplicatePrefix.CurrentCallZeroSharedBoolWindow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowView GeneralRangeMapOrigins S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem capacity {tree parentTag tag} (input : EmptyForestSharedPool.Input tree parentTag tag) :
    input.after.locations.size=tree.locations.size := by
  have shape:=congrArg (fun value=>value.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  change input.after.locations.entries.map (fun row=>(row.range,locationShape row.data))=
    tree.locations.entries.map (fun row=>(row.range,locationShape row.data)) at shape
  have ranges:=congrArg (Array.map Prod.fst) shape
  have same : input.after.locations.entries.map (·.range)=tree.locations.entries.map (·.range) := by
    simpa only [Array.map_map,Function.comp_def] using ranges
  rw [GeneralRangeMapState.size_from_ranges,same,←GeneralRangeMapState.size_from_ranges]

private theorem old_nodes {tree parentTag tag} (input : EmptyForestSharedPool.Input tree parentTag tag)
    (index : UniIndex) (node : TreeNode) (found : tree.nodes.get index=some node) :
    ∃next,input.after.nodes.get index=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission := by
  obtain ⟨next,nextAt,tagEq,parent,exposure⟩:=S03EmptySharedFrame.old_node input index node found
  obtain ⟨other,otherAt,permission⟩:=(zero_shared_rule "CurrentCallSharedConstructorFrame.old_default_of_stage") tree input.after input.index input.parent input.parentNode tag input.vacant input.present input.mapping tree.locations
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read) index node found
  have equal : other=next:=Option.some.inj (otherAt.symm.trans nextAt)
  exact ⟨next,nextAt,tagEq,parent,exposure,by rw [←equal];exact permission⟩

private theorem old_edges {tree C parentTag tag} (parents : ParentInterpretation tree C)
    (input : EmptyForestSharedPool.Input tree parentTag tag) (query origin : UniIndex)
    (edge : C.parents[query.toNat]?=some (some origin)) :
    (extend C input.index input.parent).parents[query.toNat]?=some (some origin) := by
  have different : query≠input.index := by
    intro same
    obtain ⟨node,found⟩:=(parents.edgeLive query origin edge).1
    rw [same,input.vacant] at found
    cases found
  exact (old_parent C input.index input.parent query different (Array.getElem?_eq_some_iff.mp edge).1).trans edge

/-- Counter-only weakening under the literal restored protector table. -/
theorem runtime_mono (tree : BorrowTree) (old next : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree old)
    (flags : next.protectedTags=old.protectedTags)
    (counter : old.nextPointerTag.value.toNat≤next.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree next := by
  refine ⟨by rw [flags];exact runtime.formed,by rw [flags];exact runtime.coherent,runtime.possible,⟨?_,?_⟩⟩
  · intro row member;exact Nat.lt_of_lt_of_le (runtime.below.mapping row member) counter
  · intro row member
    rw [flags] at member
    exact Nat.lt_of_lt_of_le (runtime.below.protectors row member) counter

variable (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (firstParent firstTag : BorTag) (first : EmptyForestSharedPool.Input tree firstParent firstTag)
    (secondParent secondTag : BorTag) (second : EmptyForestSharedPool.Input first.after secondParent secondTag)
    (firstRoom : tree.nodes.size+1≤4294967295) (firstBound : firstTag.value.toNat<global.nextPointerTag.value.toNat)
    (secondRoom : first.after.nodes.size+1≤4294967295) (secondBound : secondTag.value.toNat<global.nextPointerTag.value.toNat)
    (primary : ∃node,tree.nodes.get allocationRoot=some node)
    (firstOrder : first.parentNode.tag.value≤firstTag.value) (secondOrder : second.parentNode.tag.value≤secondTag.value)

abbrev completion := extend (extend C first.index first.parent) second.index second.parent

include runtime parents firstRoom firstBound secondRoom secondBound primary firstOrder secondOrder in
/-- Compose only the two actual zero constructors; no intermediate heap is
invented to install a temporary logical window. -/
theorem metadata_two :
    DuplicatePrefixBorrowContract.RuntimeFacts second.after global ∧ParentInterpretation second.after (completion tree C firstParent firstTag first secondParent secondTag second) ∧
    second.after.locations.size=tree.locations.size ∧second.after.roots=tree.roots ∧
    (∀index node,tree.nodes.get index=some node→∃next,second.after.nodes.get index=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission) ∧
    (∀(query origin : UniIndex),C.parents[query.toNat]?=some (some origin)→(completion tree C firstParent firstTag first secondParent secondTag second).parents[query.toNat]?=some (some origin)) := by
  obtain ⟨firstRuntime,firstFrame,firstParents⟩:=CurrentCallZeroSharedBoolFrame.metadata tree global C runtime parents firstParent firstTag first firstRoom firstBound primary firstOrder
  have primaryFirst : ∃node,first.after.nodes.get allocationRoot=some node := by
    obtain ⟨node,found⟩:=primary
    obtain ⟨next,nextAt,_⟩:=old_nodes first allocationRoot node found
    exact ⟨next,nextAt⟩
  obtain ⟨secondRuntime,secondFrame,secondParents⟩:=CurrentCallZeroSharedBoolFrame.metadata first.after global (extend C first.index first.parent) firstRuntime firstParents
    secondParent secondTag second secondRoom secondBound primaryFirst secondOrder
  refine ⟨secondRuntime,secondParents,(capacity second).trans (capacity first),secondFrame.roots.trans firstFrame.roots,?_,?_⟩
  · intro index node found
    obtain ⟨middle,middleAt,tag,parent,exposure,permission⟩:=old_nodes first index node found
    obtain ⟨next,nextAt,nextTag,nextParent,nextExposure,nextPermission⟩:=old_nodes second index middle middleAt
    exact ⟨next,nextAt,nextTag.trans tag,nextParent.trans parent,nextExposure.trans exposure,nextPermission.trans permission⟩
  · intro query origin edge
    exact old_edges firstParents second query origin (old_edges parents first query origin edge)

end

section Installation
variable {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (next : MachineHooks.BorrowState)
    (firstParent firstTag : BorTag) (first : EmptyForestSharedPool.Input B.allocation.extra firstParent firstTag)
    (secondParent secondTag : BorTag) (second : EmptyForestSharedPool.Input first.after secondParent secondTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (flags : next.global.protectedTags=tracker.global.protectedTags)
    (counter : tracker.global.nextPointerTag.value.toNat≤next.global.nextPointerTag.value.toNat)
    (firstRoom : B.allocation.extra.nodes.size+1≤4294967295) (firstBound : firstTag.value.toNat<next.global.nextPointerTag.value.toNat)
    (secondRoom : first.after.nodes.size+1≤4294967295) (secondBound : secondTag.value.toNat<next.global.nextPointerTag.value.toNat)
    (firstOrder : first.parentNode.tag.value≤firstTag.value) (secondOrder : second.parentNode.tag.value≤secondTag.value)

include runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder in
private theorem prepare :
    DuplicatePrefixBorrowContract.RuntimeFacts second.after next.global ∧
    ParentInterpretation second.after (completion B.allocation.extra B.precise.completion firstParent firstTag first secondParent secondTag second) ∧
    second.after.locations.size=B.allocation.extra.locations.size ∧second.after.roots=B.allocation.extra.roots ∧
    (∀index node,B.allocation.extra.nodes.get index=some node→∃changed,second.after.nodes.get index=some changed ∧changed.tag=node.tag ∧changed.parent=node.parent ∧changed.isExposed=node.isExposed ∧changed.defaultInitialPermission=node.defaultInitialPermission) ∧
    (∀(query origin : UniIndex),B.precise.completion.parents[query.toNat]?=some (some origin)→
      (completion B.allocation.extra B.precise.completion firstParent firstTag first secondParent secondTag second).parents[query.toNat]?=some (some origin)) := by
  obtain ⟨root,rootAt,_,_,_⟩:=B.issued.capability.rootNode
  exact metadata_two B.allocation.extra next.global B.precise.completion (runtime_mono _ _ _ runtime flags counter) B.parents
    firstParent firstTag first secondParent secondTag second firstRoom firstBound secondRoom secondBound ⟨root,rootAt⟩ firstOrder secondOrder

variable (post : Before) (present : Present (ActualWorld post) id (B.allocation.setExtra second.after))
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id)

include runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder present rootTag in
/-- Any originally issued Bool grant, including its retained original
return-parent obligation, reaches the actual final heap after both constructors. -/
theorem license_two {grant : UniIndex} (old : SpatialDelegation before tracker id B.allocation B.precise.completion grant) :
    SpatialDelegation post next id (B.allocation.setExtra second.after)
      (completion B.allocation.extra B.precise.completion firstParent firstTag first secondParent secondTag second) grant := by
  have facts:=prepare B next firstParent firstTag first secondParent secondTag second runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder
  apply CurrentCallAllocationLicense.spatial old post next _ present rootTag rfl rfl facts.2.2.1
  · intro position root found
    change second.after.roots[position]?=some root
    rw [facts.2.2.2.1];exact found
  · exact facts.2.2.2.2.1
  · exact facts.2.2.2.2.2

include runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder in
theorem binding_two (pointer : PointerInstance) (binding : PointerBinds B.allocation pointer) :
    PointerBinds (B.allocation.setExtra second.after) pointer := by
  have facts:=prepare B next firstParent firstTag first secondParent secondTag second runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder
  obtain ⟨node,found,_,provenance⟩:=binding
  obtain ⟨changed,changedAt,tag,parent,exposure,_⟩:=facts.2.2.2.2.1 pointer.grant node found
  refine ⟨changed,changedAt,facts.1.formed.allocator.nodeTags _ _ changedAt,?_⟩
  cases prov : pointer.value.provenance with
  | concrete supplied parentTag=>simp only [prov] at provenance ⊢;exact ⟨provenance.1,provenance.2.trans tag.symm⟩
  | wildcard=>simp only [prov] at provenance ⊢;exact exposure.trans provenance

include runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder present rootTag in
/-- Install the old Bool family only in the actual post-world after BOTH
zero constructors. Family, loan and owner slots stay fixed; only precise C
records the two real physical edges. -/
theorem window_two (start : UInt64) (startEq : start.toNat=offset) :
    ∃nextData,∃Q : UniformWindow post next nextData owner id offset 1 .ret,
      Q.pointer=B.pointer ∧Q.loan=B.loan ∧Q.allocation=B.allocation.setExtra second.after ∧
      Q.precise.completion=completion B.allocation.extra B.precise.completion firstParent firstTag first secondParent secondTag second := by
  have facts:=prepare B next firstParent firstTag first secondParent secondTag second runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder
  have firstByte:=(B.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have endFits : start.toNat+1<2^64 := by
    have cap:=UInt64.toNat_lt B.allocation.byteSize.bytes
    have extent:=B.issued.capability.extent
    omega
  have endEq : (start+1).toNat=start.toNat+1:=by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endFits]
  have initial:=(zero_shared_rule "CurrentCallExclusiveWindowFrame.window_owned") B rfl runtime start (start+1) (by omega) (by omega)
  have initialFuture : OwnedOn (Authority B.allocation.extra B.precise.completion next.global.protectedTags B.pointer.grant) start (start+1) B.allocation.extra.locations := by rw [flags];exact initial
  obtain ⟨root,rootAt,_,_,_⟩:=B.issued.capability.rootNode
  obtain ⟨firstRuntime,firstFrame,firstParents⟩:=CurrentCallZeroSharedBoolFrame.metadata B.allocation.extra next.global B.precise.completion
    (runtime_mono _ _ _ runtime flags counter) B.parents firstParent firstTag first firstRoom firstBound ⟨root,rootAt⟩ firstOrder
  obtain ⟨oldNode,oldAt,_,_⟩:=B.binding
  obtain ⟨middle,middleAt,_⟩:=old_nodes first B.pointer.grant oldNode oldAt
  have firstOwned:=CurrentCallZeroSharedBoolFrame.owned B.allocation.extra B.precise.completion next.global.protectedTags B.parents firstParent firstTag first
    B.pointer.grant ⟨oldNode,oldAt⟩ start (start+1) initialFuture
  have finalOwned:=CurrentCallZeroSharedBoolFrame.owned first.after (extend B.precise.completion first.index first.parent) next.global.protectedTags firstParents secondParent secondTag second
    B.pointer.grant ⟨middle,middleAt⟩ start (start+1) firstOwned
  let Cnew:=completion B.allocation.extra B.precise.completion firstParent firstTag first secondParent secondTag second
  let nextData : Identities:={data with interpretation:={data.interpretation with precise:=data.interpretation.precise.push (id,{B.precise with completion:=Cnew})}}
  have issued:=license_two B next firstParent firstTag first secondParent secondTag second runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder post present rootTag B.issued
  have binding:=binding_two B next firstParent firstTag first secondParent secondTag second runtime flags counter firstRoom firstBound secondRoom secondBound firstOrder secondOrder B.pointer B.binding
  let Q : UniformWindow post next nextData owner id offset 1 .ret:={
    loan:=B.loan,pointer:=B.pointer,allocation:=B.allocation.setExtra second.after,precise:={B.precise with completion:=Cnew}
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId,present:=present,preciseAt:=by simp [nextData]
    binding:=binding,issued:=issued,parents:=facts.2.1,window:=by
      intro byte inside
      refine ⟨(B.window byte inside).1,?_⟩
      intro segment member lower upper index node found
      obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      subst segment
      change second.after.locations.entries[position].range.start.toNat≤byte.2 at lower
      change byte.2<second.after.locations.entries[position].range.stop.toNat at upper
      have rights:=finalOwned position valid (by omega) (by have h:=inside.2;omega) (by have h:=inside.2;omega) index node found
      have realized:=CandidateCurrentGrantRuntime.realized _ _ (facts.1.possible position valid index node found) ((facts.1.formed.profile position valid).present index node found)
      exact ⟨fun below=>(zero_shared_rule "CurrentCallResourceCopyInstall.local_token") _ _ realized (rights.1 below),
        fun clash=>Classical.byContradiction (fun outside=>(zero_shared_rule "CurrentCallResourceCopyInstall.foreign_no_clash") _ _ realized (rights.2 outside) clash)⟩}
  exact ⟨nextData,Q,rfl,rfl,rfl,rfl⟩
end Installation

end DuplicatePrefix.CurrentCallZeroSharedBoolWindow

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallZeroSharedBoolWindow" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual two-zero Shared Bool installation dependency {dependency}"
