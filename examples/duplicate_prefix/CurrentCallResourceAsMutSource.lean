import duplicate_prefix.CurrentCallResourceAsMutInvoke
import duplicate_prefix.CurrentCallResourceAsMutBoolFrame
import duplicate_prefix.CurrentCallResourceLenActivity

namespace DuplicatePrefix.CurrentCallResourceAsMutSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization CurrentCallResourceEntryBody
open GeneralRangeMapOrigins S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem release_nodes (tree : BorrowTree) (flags : ProtectedTags) (tag : BorTag) :
    (tree.releaseProtector tag flags).tree.nodes=tree.nodes := by
  have nodes:=congrArg BorrowTree.nodes (GeneralBorrowStructuralReleaseGeometryFrame.release tree flags tag)
  exact nodes

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


variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

abbrev tree := CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
abbrev completion := CurrentCallResourceAsMutReturn.completion done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
abbrev postTracker := CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
abbrev allocation := done.current.allocation.setExtra (tree done fresh valid15 seed)

/-- Real S→P→q edges and actual post-endCall unheld nodes. Neither old q nor
its Default child is assumed to be a leaf. -/
structure Chain where
  childNode : TreeNode
  parentNode : TreeNode
  childAt : (tree done fresh valid15 seed).nodes.get seed.childIndex=some childNode
  parentAt : (tree done fresh valid15 seed).nodes.get done.current.pointer.grant=some parentNode
  childEdge : (completion done fresh valid15 seed).parents[seed.childIndex.toNat]?=some (some done.current.pointer.grant)
  parentEdge : (completion done fresh valid15 seed).parents[done.current.pointer.grant.toNat]?=some (some done.qWindow.pointer.grant)
  childUnheld : (postTracker done fresh valid15 seed).global.protectedTags.contains childNode.tag=false
  parentUnheld : (postTracker done fresh valid15 seed).global.protectedTags.contains parentNode.tag=false

private theorem parent_grant : done.current.pointer.grant=done.stage.childIndex := by rw [done.pointer];rfl

private theorem flags : (postTracker done fresh valid15 seed).global.protectedTags=done.nextTracker.global.protectedTags :=
  CurrentCallResourceAsMutBoolFrame.flags done.current done.entry done.frame done.base _ fresh valid15 seed

theorem chain : Nonempty (Chain done fresh valid15 seed) := by
  obtain ⟨child,childAt,childTag,childHidden⟩:=seed.hidden
  have childFinal : (tree done fresh valid15 seed).nodes.get seed.childIndex=some child:=by
    rw [tree,CurrentCallResourceAsMutReturn.releasedTree,release_nodes]
    exact childAt
  have pAt : done.current.allocation.extra.nodes.get done.stage.childIndex=some done.stage.node := by
    rw [done.allocation]
    exact done.stage.nodeAt
  obtain ⟨parent,parentAt,parentTag,parentParent,parentHidden,parentPermission⟩:=
    CurrentCallResourceAsMutBoolFrame.metadata done.current done.entry done.frame done.base _ fresh valid15 seed done.stage.childIndex done.stage.node pAt
  have parentFinal : (tree done fresh valid15 seed).nodes.get done.current.pointer.grant=some parent:=by
    rw [parent_grant done]
    exact parentAt
  have edge : done.current.precise.completion.parents[done.current.pointer.grant.toNat]?=some (some done.qWindow.pointer.grant) := by
    rw [done.completion,parent_grant done]
    exact child_edge _ _ _
  have finalEdge:=CurrentCallResourceAsMutBoolFrame.old_edge done.current done.entry done.frame done.base _ fresh valid15 seed _ _ edge
  have member : (id,child.tag)∈seed.output.frame.protectedTags.toList:=by rw [seed.frameOwned,childTag];simp
  have childUnheld:=GeneralBorrowRelease.end_call_owned_absent seed.output.global seed.output.frame id child.tag member
  have parentUnheld : (postTracker done fresh valid15 seed).global.protectedTags.contains parent.tag=false := by
    rw [flags done fresh valid15 seed,parentTag,done.stage.nodeTag]
    exact done.stage.unheld
  exact ⟨⟨child,parent,childFinal,parentFinal,child_edge _ _ _,finalEdge,childUnheld,parentUnheld⟩⟩

/-- Reanchor full current S rights on any locations-updated tree under the
actual fixed post-endCall flags. This is consumed after the real copy. -/
theorem copy_owned (afterTree : BorrowTree) (nodes : afterTree.nodes=(tree done fresh valid15 seed).nodes)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority afterTree (completion done fresh valid15 seed)
      (postTracker done fresh valid15 seed).global.protectedTags seed.childIndex)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) afterTree.locations) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority afterTree (completion done fresh valid15 seed)
      (postTracker done fresh valid15 seed).global.protectedTags done.qWindow.pointer.grant)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) afterTree.locations := by
  obtain ⟨chain⟩:=chain done fresh valid15 seed
  have childAt : afterTree.nodes.get seed.childIndex=some chain.childNode:=by rw [nodes];exact chain.childAt
  have parentAt : afterTree.nodes.get done.current.pointer.grant=some chain.parentNode:=by rw [nodes];exact chain.parentAt
  intro cursor valid positive start stop
  have parentOwned:=S05CompletedChildReanchor.authority afterTree _ _ _ _ _ _ chain.childNode chain.childEdge childAt
    (fun _ held=>held) chain.childUnheld (owned cursor valid positive start stop)
  exact S05CompletedChildReanchor.authority afterTree _ _ _ _ _ _ chain.parentNode chain.parentEdge parentAt
    (fun _ held=>held) chain.parentUnheld parentOwned

theorem owned : OwnedOn (S05CompletedAncestryReadMutable.Authority (tree done fresh valid15 seed) (completion done fresh valid15 seed)
    (postTracker done fresh valid15 seed).global.protectedTags done.qWindow.pointer.grant)
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) (tree done fresh valid15 seed).locations :=
  copy_owned done fresh valid15 seed _ rfl (CurrentCallResourceAsMutReturn.owned_end_call done.current done.entry done.frame done.base _ fresh valid15 seed)

theorem activity : GeneralBorrowFreshActiveWithin.ActiveWithin (tree done fresh valid15 seed) out.sourceChild .Write
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  have oldActive:=(CurrentCallResourceLenActivity.resources out ready result).activity
  have pActive : GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceAsMutInvoke.defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)
      out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
    apply done.stage.targetActivity
    rw [done.qAllocation]
    simpa only [CurrentCallResourceAsMutInvoke.sourceEntry,CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using oldActive
  have pCurrent : GeneralBorrowFreshActiveWithin.ActiveWithin done.current.allocation.extra out.sourceChild .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by rw [done.allocation];exact pActive
  have sActive:=seed.targetActivity out.sourceChild pCurrent
  obtain ⟨node,nodeAt,nodeTag,hidden⟩:=seed.hidden
  exact GeneralBorrowActiveWithinRelease.release seed.output.child.tree seed.output.global.protectedTags seed.output.tag seed.childIndex out.sourceChild
    node seed.lookup nodeAt hidden (UInt64.ofNat offset) (UInt64.ofNat offset+len) seed.activity sActive


theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts (tree done fresh valid15 seed) (postTracker done fresh valid15 seed).global :=
  CurrentCallResourceAsMutReturn.runtime_end_call done.current done.entry done.frame done.base _ fresh valid15 seed

theorem parents : ParentInterpretation (tree done fresh valid15 seed) (completion done fresh valid15 seed) :=
  CurrentCallResourceAsMutBoolFrame.parents done.current done.entry done.frame done.base _ fresh valid15 seed

theorem roots : (tree done fresh valid15 seed).roots.toList.Nodup :=
  CurrentCallResourceAsMutBoolFrame.roots done.current done.entry done.frame done.base _ fresh valid15 seed

theorem short : (tree done fresh valid15 seed).nodes.size<65536 :=
  CurrentCallResourceAsMutBoolFrame.short done.current done.entry done.frame done.base _ fresh valid15 seed

private theorem p_vacant : done.qWindow.allocation.extra.nodes.get done.stage.childIndex=none := by
  have frame:=GeneralBorrowFreshReadFrame.frame done.qWindow.allocation.extra (.concrete out.sourceOutput.tag)
    (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes len) .Read
    (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags .VisitChildrenOfAccessed
  have nodes:=congrArg BorrowTree.nodes frame
  have absent:=done.stage.leaf.vacant
  dsimp only [GeneralBorrowRawDefaultExpression.read,GeneralBorrowRawSharedExpression.read] at absent
  rw [nodes] at absent
  exact absent

private theorem p_license {grant : UniIndex}
    (old : SpatialDelegation (CurrentCallResourceAsMutInvoke.beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) id
      done.qWindow.allocation done.qWindow.precise.completion grant) :
    SpatialDelegation done.machine done.nextTracker id done.current.allocation done.current.precise.completion grant := by
  have present:=done.current.present
  rw [done.allocation] at present
  have issued:=CurrentCallResourceInstallation.spatial old done.qWindow.parents done.machine done.nextTracker
    (CurrentCallResourceAsMutInvoke.defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len) present rfl
    done.stage.capacity (fun position root slot=>by rw [done.stage.roots];exact slot) done.stage.oldNodes done.stage.childIndex
    done.qWindow.pointer.grant (p_vacant done)
  rw [done.allocation,done.completion]
  exact issued

/-- Any old source-allocation issuance follows the two real extensions into
this actual post-return world. It is separate from current mutable contents. -/
theorem license {grant : UniIndex}
    (old : SpatialDelegation (CurrentCallResourceAsMutInvoke.beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) id
      done.qWindow.allocation done.qWindow.precise.completion grant) :
    SpatialDelegation returned.machine (postTracker done fresh valid15 seed) id
      (allocation done fresh valid15 seed) (completion done fresh valid15 seed) grant :=
  CurrentCallResourceAsMutBoolFrame.license done.current done.entry done.frame done.base _ fresh valid15 seed returned (p_license done old)

private theorem p_binding (pointer : PointerInstance) (old : PointerBinds done.qWindow.allocation pointer) :
    PointerBinds done.current.allocation pointer := by
  rw [done.allocation]
  obtain ⟨node,atNode,mapped,binding⟩:=old
  obtain ⟨next,nextAt,tag,_,exposure,_⟩:=done.stage.oldNodes pointer.grant node atNode
  refine ⟨next,nextAt,done.stage.runtime.formed.allocator.nodeTags _ _ nextAt,?_⟩
  cases prov : pointer.value.provenance with
  | concrete supplied oldTag=>simp only [prov] at binding ⊢;exact ⟨binding.1,binding.2.trans tag.symm⟩
  | wildcard=>simp only [prov] at binding ⊢;exact exposure.trans binding

theorem binding (pointer : PointerInstance) (old : PointerBinds done.qWindow.allocation pointer) :
    PointerBinds (allocation done fresh valid15 seed) pointer :=
  CurrentCallResourceAsMutBoolFrame.old_binding done.current done.entry done.frame done.base _ fresh valid15 seed pointer (p_binding done pointer old)


theorem grant : done.qWindow.pointer.grant=out.sourceChild := by
  have equal:=congrArg PointerInstance.grant (done.qPointer.trans result.sourcePointer)
  simpa only [CurrentCallResourceSourceAfterBool.pointer,CurrentCallResourceFnEntry.child_pointer] using equal

theorem node : ∃ node,(tree done fresh valid15 seed).nodes.get out.sourceChild=some node ∧
    node.tag=out.sourceOutput.tag ∧node.isExposed=false := by
  have oldAt : done.qWindow.allocation.extra.nodes.get out.sourceChild=some result.sourceNode := by
    rw [done.qAllocation]
    have found:=result.sourceAt
    have indexEq : Q.pointer.grant=out.sourceChild:=(congrArg PointerInstance.grant done.qPointer).symm.trans (grant done)
    rw [indexEq] at found
    simpa only [CurrentCallResourceAsMutInvoke.sourceEntry,CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using found
  obtain ⟨p,pAt,pTag,_,pHidden,_⟩:=done.stage.oldNodes out.sourceChild result.sourceNode oldAt
  have present : done.current.allocation.extra.nodes.get out.sourceChild=some p := by
    rw [done.allocation]
    simpa only [Allocation.setExtra,Allocation.mapExtra] using pAt
  obtain ⟨next,nextAt,nextTag,_,nextHidden,_⟩:=CurrentCallResourceAsMutBoolFrame.metadata done.current done.entry done.frame done.base _ fresh valid15 seed out.sourceChild p present
  exact ⟨next,nextAt,nextTag.trans (pTag.trans result.sourceTag),nextHidden.trans (pHidden.trans (CurrentCallResourceLenActivity.resources out ready result).hidden)⟩


private theorem q_window (byte : CandidateFreezeContentResources.Byte) (inside : Window id offset len.toNat byte) :
    byte.2<(allocation done fresh valid15 seed).len ∧
    Embeds (allocation done fresh valid15 seed) (postTracker done fresh valid15 seed).global.protectedTags
      (completion done fresh valid15 seed) done.qWindow.pointer.grant byte.2 .exclusive := by
  have startEq:=(CurrentCallResourceSharedStage.source_bounds out).1
  have original:=(done.qWindow.window byte (by simpa only [startEq] using inside)).1
  have lenEq:=congrArg Allocation.len done.allocation
  dsimp only [Allocation.setExtra,Allocation.mapExtra] at lenEq
  refine ⟨?_,?_⟩
  · change byte.2<done.current.allocation.len
    rw [lenEq]
    exact original
  · have capacity:=(CurrentCallResourceAsMutReturn.release done.current done.entry done.frame done.base _ fresh valid15 seed).2.2.2.2.1
    have bounds:=seed.bounds
    rw [←capacity] at bounds
    have noWrap : (UInt64.ofNat offset).toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
    have endEq : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by
      simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
    have lowerByte : (UInt64.ofNat offset).toNat≤byte.2:=by have interval:=inside.2;omega
    have upperByte : byte.2<(UInt64.ofNat offset+len).toNat:=by have interval:=inside.2;omega
    intro segment member lower upper index node found
    dsimp only [allocation,Allocation.setExtra,Allocation.mapExtra] at member lower upper found ⊢
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have rights:=owned done fresh valid15 seed position valid (by omega) (by omega) (by omega) index node found
    have currentRuntime:=runtime done fresh valid15 seed
    have realized:=CandidateCurrentGrantRuntime.realized _ _ (currentRuntime.possible position valid index node found)
      ((currentRuntime.formed.profile position valid).present index node found)
    constructor
    · intro below
      exact local_token _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact foreign_no_clash _ _ realized (rights.2 outside) clash

private def viewData : Identities:={done.qData with interpretation:={done.qData.interpretation with
  pointers:=done.qData.interpretation.pointers.push done.qWindow.pointer
  loans:=done.qData.interpretation.loans.push ⟨done.qData.interpretation.pointers.size,some done.qOwner,done.qWindow.loan.depth⟩
  precise:=done.qData.interpretation.precise.push (id,{done.qWindow.precise with completion:=completion done fresh valid15 seed})}}

private def view : UniformWindow returned.machine (postTracker done fresh valid15 seed)
    (viewData done fresh valid15 seed) done.qData.interpretation.loans.size id offset len.toNat .mut where
  loan:=⟨done.qData.interpretation.pointers.size,some done.qOwner,done.qWindow.loan.depth⟩
  pointer:=done.qWindow.pointer
  allocation:=allocation done fresh valid15 seed
  precise:={done.qWindow.precise with completion:=completion done fresh valid15 seed}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=done.qWindow.pointerId
  present:=(license done fresh valid15 seed returned done.qWindow.issued).capability.live
  preciseAt:=by simp [viewData]
  binding:=binding done fresh valid15 seed done.qWindow.pointer done.qWindow.binding
  issued:=license done fresh valid15 seed returned done.qWindow.issued
  parents:=parents done fresh valid15 seed
  window:=q_window done fresh valid15 seed

/-- A technical actual q view after the real mutable helper endCall/pop. This
neither assumes q is a leaf nor asserts a whole post CurrentDenotation. -/
theorem current : ∃ currentData currentOwner,
    ∃ current : UniformWindow returned.machine (postTracker done fresh valid15 seed) currentData currentOwner id offset len.toNat .mut,
      current.pointer=Q.pointer ∧current.allocation=allocation done fresh valid15 seed ∧
      current.precise.completion=completion done fresh valid15 seed :=
  ⟨viewData done fresh valid15 seed,done.qData.interpretation.loans.size,view done fresh valid15 seed returned,done.qPointer,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallResourceAsMutSource
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAsMutSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual AsMut source resource dependency {dependency}"
