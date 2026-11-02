import duplicate_prefix.CurrentCallResourceLenActivity
import duplicate_prefix.CurrentCallResourceLenBoolFrame
import duplicate_prefix.CurrentCallResourceLenCapability
import duplicate_prefix.CurrentCallResourceBoolCurrent

namespace DuplicatePrefix.CurrentCallResourceLenBoolCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization CurrentCallResourceEntryBody
open GeneralRangeMapOrigins GeneralBorrowFnEntryRegistration S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
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


private theorem insert_remove (tags : ProtectedTags) (tag : BorTag)
    (different : ∀ row∈tags.entries,row.1≠tag) : (tags.insert tag .StrongProtector).remove tag=tags := by
  have unchanged : tags.entries.filter (fun row=>row.1!=tag)=tags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    simpa only [bne_iff_ne] using different row member
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,unchanged]

private theorem issue_on {before : Before} {tracker : MachineHooks.BorrowState} {id : AllocId}
    {allocation : Allocation Provenance BorrowTree} {tree : BorrowTree} {completion : Completion} {grant : UniIndex}
    (cap : AllocationCapability before tracker id allocation) (treeEq : allocation.extra=tree)
    (parents : ParentInterpretation tree completion) (below : Below completion allocationRoot grant) :
    SpatialDelegation before tracker id allocation completion grant := by
  cases treeEq
  exact CurrentCallResourceLenCapability.issued_of_rootBelow cap parents below

private theorem spatial_at_id {before : Before} {tracker : MachineHooks.BorrowState} {oldId newId : AllocId}
    {allocation : Allocation Provenance BorrowTree} {completion : Completion} {grant : UniIndex}
    (same : oldId=newId) (issued : SpatialDelegation before tracker oldId allocation completion grant) :
    SpatialDelegation before tracker newId allocation completion grant := by
  cases same
  exact issued

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)
    {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)

abbrev allocation := CurrentCallResourceLenBoolFrame.boolAllocation out ready
abbrev completion := CurrentCallResourceLenBoolFrame.boolCompletion out ready returned

theorem allocation_same (same : out.physical.id=id) : allocation out ready=CurrentCallResourceLenCapability.sourceAllocation out ready := by
  dsimp only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,CurrentCallResourceLenCapability.sourceAllocation]
  rw [ite_eq_left same]

theorem tree_same (same : out.physical.id=id) : (allocation out ready).extra=CurrentCallResourceLenReturn.releasedTree out ready := by
  have equal:=congrArg Allocation.extra (allocation_same out ready same)
  dsimp only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] at equal
  exact equal

theorem completion_same (same : out.physical.id=id) : completion out ready returned=returned.completion := by
  dsimp only [completion,CurrentCallResourceLenBoolFrame.boolCompletion]
  rw [ite_eq_left same]

private theorem source_extra : (CurrentCallResourceLenCapability.sourceAllocation out ready).extra=CurrentCallResourceLenReturn.releasedTree out ready := by
  dsimp only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra]

include returned in
private theorem old_completion (same : out.physical.id=id) : Q.precise.completion=CurrentCallResourceBoolCurrent.completion out := by
  rw [returned.sourceCompletion]
  dsimp only [CurrentCallResourceSourceFinal.completion,CurrentCallResourceBoolCurrent.completion]
  rw [ite_eq_left same]

private theorem post_flags : (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags=out.boolOutput.global.protectedTags := by
  change (out.boolOutput.global.protectedTags.insert (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag .StrongProtector).remove
    (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag=out.boolOutput.global.protectedTags
  apply insert_remove
  intro row member same
  have bound:=out.afterRuntime.below.protectors row member
  rw [same] at bound
  have successor:=GenericFunctionEntryNumerics.successor_value out.boolOutput.global.nextPointerTag (CurrentCallResourceBodyReadiness.current_room out ready)
  change (TypedRetagEmpty.successorTag out.boolOutput.global.nextPointerTag (CurrentCallResourceBodyReadiness.current_room out ready)).value.toNat<out.boolOutput.global.nextPointerTag.value.toNat at bound
  omega

private theorem post_raise : out.boolOutput.global.nextPointerTag.value.toNat≤(CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value.toNat := by
  have first:=GenericFunctionEntryNumerics.successor_value out.boolOutput.global.nextPointerTag (CurrentCallResourceBodyReadiness.current_room out ready)
  have second:=GenericFunctionEntryNumerics.successor_value (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (CurrentCallResourceLenInvoke.helper_room out ready)
  change out.boolOutput.global.nextPointerTag.value.toNat≤(TypedRetagEmpty.successorTag (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (CurrentCallResourceLenInvoke.helper_room out ready)).value.toNat
  rw [second]
  change out.boolOutput.global.nextPointerTag.value.toNat≤(TypedRetagEmpty.successorTag out.boolOutput.global.nextPointerTag (CurrentCallResourceBodyReadiness.current_room out ready)).value.toNat+1
  omega

include returned in
theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts (allocation out ready).extra (CurrentCallResourceLenReturn.postTracker out ready).global := by
  by_cases same : out.physical.id=id
  · rw [tree_same out ready same]
    exact returned.runtime
  · have formed:=out.afterRuntime.formed
    have coherent:=out.afterRuntime.coherent
    have possible:=out.afterRuntime.possible
    have below:=GeneralBorrowForestTagHighWaterHistory.weaken out.updated.extra out.boolOutput.global.protectedTags out.boolOutput.global.nextPointerTag
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag out.afterRuntime.below (post_raise out ready)
    rw [←post_flags out ready] at formed coherent below
    simpa only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same] using
      (show DuplicatePrefixBorrowContract.RuntimeFacts out.updated.extra (CurrentCallResourceLenReturn.postTracker out ready).global from ⟨formed,coherent,possible,below⟩)

theorem parents : ParentInterpretation (allocation out ready).extra (completion out ready returned) := by
  by_cases same : out.physical.id=id
  · rw [tree_same out ready same,completion_same out ready returned same]
    exact returned.parents
  · simpa only [allocation,completion,CurrentCallResourceLenBoolFrame.boolAllocation,CurrentCallResourceLenBoolFrame.boolCompletion,ite_eq_right same] using out.afterParents

include returned in
theorem roots : (allocation out ready).extra.roots.toList.Nodup := by
  by_cases same : out.physical.id=id
  · rw [tree_same out ready same]
    have frame:=CurrentCallResourceLenActivity.resources out ready returned
    rw [frame.roots,returned.sourceAllocation]
    exact CurrentCallResourceSourceFinal.roots out
  · have original:=out.finalRoots (out.physical.id,{out.physical.entry with allocation:=out.updated})
      (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (CurrentCallResourceBoolCurrent.live out)))
    simpa only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same] using original

include returned in
theorem short : (allocation out ready).extra.nodes.size<65536 := by
  by_cases same : out.physical.id=id
  · rw [tree_same out ready same]
    exact returned.short
  · have growth:=CurrentCallResourceEntryFacets.bool_growth out
    rw [(out.otherTree (fun equal=>same (out.physicalId.trans equal))).1] at growth
    have nodeSize:=congrArg (fun nodes : UniValMap TreeNode=>nodes.size) out.updatedNodes
    have room:=C.boolRoom
    simp only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same]
    omega

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  if out.physical.id=id then {(CurrentCallResourceLenInvoke.entry out) with allocation:=allocation out ready}
  else {out.physical.entry with allocation:=allocation out ready}

theorem entry_allocation : (entry out ready).allocation=allocation out ready := by
  by_cases same : out.physical.id=id <;>simp only [entry,same,↓reduceIte]

theorem live : returned.machine.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,entry out ready) := by
  by_cases same : out.physical.id=id
  · have actual:=returned.sourceLive
    simpa only [entry,ite_eq_left same,same,↓reduceIte,allocation_same out ready same,CurrentCallResourceLenCapability.sourceAllocation] using actual
  · simp only [entry,allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same]
    rw [returned.memory]
    exact StackPopRelease.lookup_commit_other (CurrentCallResourceSharedStage.afterMachine out ready).memory id out.physical.id
      (CurrentCallResourceLenInvoke.entry out) {out.physical.entry with allocation:=out.updated}
      (CurrentCallResourceLenReturn.releasedTree out ready) same (CurrentCallResourceLenBoolFrame.different_live_before out ready same)

theorem parent_issued : SpatialDelegation returned.machine (CurrentCallResourceLenReturn.postTracker out ready) out.physical.id
    (allocation out ready) (completion out ready returned) C.V.pointer.grant := by
  by_cases same : out.physical.id=id
  · have frame:=CurrentCallResourceLenActivity.resources out ready returned
    have before:= (CurrentCallResourceBoolCurrent.parent_issued out).root_below out.afterParents
    have beforeQ : Below Q.precise.completion allocationRoot C.V.pointer.grant := by rw [old_completion out ready returned same];exact before
    have issued:=issue_on (tree:=CurrentCallResourceLenReturn.releasedTree out ready)
      (allocation:=CurrentCallResourceLenCapability.sourceAllocation out ready) (completion:=returned.completion)
      (CurrentCallResourceLenCapability.capability out ready returned) (source_extra out ready) returned.parents (frame.below _ _ beforeQ)
    rw [allocation_same out ready same,completion_same out ready returned same]
    exact spatial_at_id same.symm issued
  · have present:=(CurrentCallResourceLenBoolFrame.result out ready returned).1
    simp only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same] at present ⊢
    simp only [completion,CurrentCallResourceLenBoolFrame.boolCompletion,ite_eq_right same]
    exact CurrentCallAllocationLicense.spatial (CurrentCallResourceBoolCurrent.parent_issued out) returned.machine
      (CurrentCallResourceLenReturn.postTracker out ready) out.updated present rfl rfl rfl rfl
      (fun _ _ found=>found) (fun _ node found=>⟨node,found,rfl,rfl,rfl,rfl⟩) _ (fun _ _ edge=>edge)

theorem issued : SpatialDelegation returned.machine (CurrentCallResourceLenReturn.postTracker out ready) out.physical.id
    (allocation out ready) (completion out ready returned) out.boolChild := by
  by_cases same : out.physical.id=id
  · have frame:=CurrentCallResourceLenActivity.resources out ready returned
    have before:=(CurrentCallResourceBoolCurrent.issued out).root_below out.afterParents
    have beforeQ : Below Q.precise.completion allocationRoot out.boolChild := by rw [old_completion out ready returned same];exact before
    have issued:=issue_on (tree:=CurrentCallResourceLenReturn.releasedTree out ready)
      (allocation:=CurrentCallResourceLenCapability.sourceAllocation out ready) (completion:=returned.completion)
      (CurrentCallResourceLenCapability.capability out ready returned) (source_extra out ready) returned.parents (frame.below _ _ beforeQ)
    rw [allocation_same out ready same,completion_same out ready returned same]
    exact spatial_at_id same.symm issued
  · have present:=(CurrentCallResourceLenBoolFrame.result out ready returned).1
    simp only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same] at present ⊢
    simp only [completion,CurrentCallResourceLenBoolFrame.boolCompletion,ite_eq_right same]
    exact CurrentCallAllocationLicense.spatial (CurrentCallResourceBoolCurrent.issued out) returned.machine
      (CurrentCallResourceLenReturn.postTracker out ready) out.updated present rfl rfl rfl rfl
      (fun _ _ found=>found) (fun _ node found=>⟨node,found,rfl,rfl,rfl,rfl⟩) _ (fun _ _ edge=>edge)

include returned in
theorem parent_binding : PointerBinds (allocation out ready) C.V.pointer := by
  by_cases same : out.physical.id=id
  · obtain ⟨node,found,_,bound⟩:=CurrentCallResourceBoolCurrent.parent_binding out
    have initial : Q.allocation=out.updated := by rw [returned.sourceAllocation,CurrentCallResourceSourceFinal.entry,ite_eq_left same]
    have foundQ : Q.allocation.extra.nodes.get C.V.pointer.grant=some node := by rw [initial];exact found
    obtain ⟨next,nextAt,tag,_,exposed⟩:=(CurrentCallResourceLenActivity.resources out ready returned).metadata _ _ foundQ
    rw [allocation_same out ready same]
    dsimp only [PointerBinds,CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra]
    have current:=runtime out ready returned
    rw [allocation_same out ready same] at current
    dsimp only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] at current
    refine ⟨next,nextAt,current.formed.allocator.nodeTags _ _ nextAt,?_⟩
    cases provenance : C.V.pointer.value.provenance with
    | concrete id tagValue=>simp only [provenance] at bound ⊢;exact ⟨bound.1,bound.2.trans tag.symm⟩
    | wildcard=>simp only [provenance] at bound ⊢;exact exposed.trans bound
  · simpa only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same] using CurrentCallResourceBoolCurrent.parent_binding out

include returned in
theorem binding : PointerBinds (allocation out ready) (CurrentCallResourceBoolCurrent.pointer out) := by
  obtain ⟨_,_,⟨node,present,tag,_,_,_⟩,_⟩:=CurrentCallResourceLenBoolFrame.result out ready returned
  refine ⟨node,present,(runtime out ready returned).formed.allocator.nodeTags _ _ present,?_⟩
  change out.physical.id=out.physical.id ∧out.boolOutput.tag=node.tag
  exact ⟨rfl,(tag.trans out.boolNodeTag).symm⟩

theorem edge : (completion out ready returned).parents[out.boolChild.toNat]?=some (some C.V.pointer.grant) := by
  by_cases same : out.physical.id=id
  · have original:=child_edge out.R.completion out.boolChild C.V.pointer.grant
    have originalQ : Q.precise.completion.parents[out.boolChild.toNat]?=some (some C.V.pointer.grant) := by rw [old_completion out ready returned same];exact original
    rw [completion_same out ready returned same]
    exact (CurrentCallResourceLenActivity.resources out ready returned).edges _ _ originalQ
  · simpa only [completion,CurrentCallResourceLenBoolFrame.boolCompletion,ite_eq_right same] using child_edge out.R.completion out.boolChild C.V.pointer.grant

private theorem length : (allocation out ready).len=out.updated.len := by
  by_cases same : out.physical.id=id
  · simp only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,CurrentCallResourceLenInvoke.entry,
      CurrentCallResourceSourceFinal.entry,ite_eq_left same,Allocation.setExtra,Allocation.mapExtra,Allocation.len]
  · simp only [allocation,CurrentCallResourceLenBoolFrame.boolAllocation,ite_eq_right same]

theorem window (byte : CandidateFreezeContentResources.Byte) (inside : Window out.physical.id out.physical.offset.toNat 1 byte) :
    byte.2<(allocation out ready).len ∧Embeds (allocation out ready) (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags
      (completion out ready returned) out.boolChild byte.2 .exclusive := by
  have bounds:=out.physical.bounds
  have fits:=out.physical.capacity.toNat_lt
  have endFits : out.physical.offset.toNat+1<2^64:=by omega
  have endEq : (out.physical.offset+1).toNat=out.physical.offset.toNat+1:=by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endFits]
  refine ⟨by rw [length out ready,out.updatedLength,out.physical.bytes];have interval:=inside.2;omega,?_⟩
  intro segment member lower upper index node present
  dsimp only [allocation,completion] at member lower upper present ⊢
  obtain ⟨position,valid,sameSegment⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have interval:=inside.2
  have owned:=(CurrentCallResourceLenBoolFrame.result out ready returned).2.1
  have rights:=owned position valid (by omega) (by omega) (by omega) index node present
  have current:=runtime out ready returned
  have realized:=CandidateCurrentGrantRuntime.realized _ _ (current.possible position valid index node present)
    ((current.formed.profile position valid).present index node present)
  exact ⟨fun below=>local_token _ _ realized (rights.1 below),fun clash=>Classical.byContradiction (fun outside=>foreign_no_clash _ _ realized (rights.2 outside) clash)⟩

/-- A precise view of this active Bool window, without a whole-denotation validity claim. -/
private def viewData : Identities := {data with interpretation:={data.interpretation with
    pointers:=data.interpretation.pointers.push (CurrentCallResourceBoolCurrent.pointer out)
    loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,some C.returnOwner,C.V.loan.depth+1⟩
    precise:=data.interpretation.precise.push (out.physical.id,{C.V.precise with completion:=completion out ready returned})}}

private def view : UniformWindow returned.machine (CurrentCallResourceLenReturn.postTracker out ready) (viewData out ready returned)
    data.interpretation.loans.size out.physical.id out.physical.offset.toNat 1 .ret where
  loan:=⟨data.interpretation.pointers.size,some C.returnOwner,C.V.loan.depth+1⟩
  pointer:=CurrentCallResourceBoolCurrent.pointer out
  allocation:=(allocation out ready)
  precise:={C.V.precise with completion:=completion out ready returned}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=rfl
  present:=(CurrentCallResourceLenBoolFrame.result out ready returned).1
  preciseAt:=by simp [viewData]
  binding:=binding out ready returned
  issued:=issued out ready returned
  parents:=parents out ready returned
  window:=window out ready returned

theorem current : ∃ nextData nextOwner,
    ∃ B : UniformWindow returned.machine (CurrentCallResourceLenReturn.postTracker out ready) nextData nextOwner out.physical.id out.physical.offset.toNat 1 .ret,
      B.pointer=CurrentCallResourceBoolCurrent.pointer out ∧ B.allocation=(allocation out ready) ∧ B.precise.completion=completion out ready returned :=
  ⟨viewData out ready returned,data.interpretation.loans.size,view out ready returned,rfl,rfl,rfl⟩


end
end DuplicatePrefix.CurrentCallResourceLenBoolCurrent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenBoolCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len Bool current dependency {dependency}"
