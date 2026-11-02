import duplicate_prefix.CurrentCallResourceRelease
import duplicate_prefix.CurrentCallResourceAsMutCall
import duplicate_prefix.CurrentCallBorrowIssuance
import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.S05CompletedChildReanchor
import duplicate_prefix.AsMutReturnFromReleaseRuntime
namespace DuplicatePrefix.CurrentCallResourceAsMutReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem owned_unheld_parent (tree : BorrowTree) (completion : Completion) (flags : ProtectedTags)
    (child parent : UniIndex) (node : TreeNode) (lower upper : UInt64)
    (edge : completion.parents[child.toNat]?=some (some parent)) (present : tree.nodes.get child=some node)
    (unheld : flags.contains node.tag=false)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion flags child) lower upper tree.locations) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion flags parent) lower upper tree.locations := by
  intro cursor valid positive start stop
  exact S05CompletedChildReanchor.authority tree completion _ flags flags child parent node edge present
    (fun _ held=>held) unheld (owned cursor valid positive start stop)

/-- A mutable helper's released child reanchors its real unprotected parent,
then the retained root source, under the actual helper endCall flags. -/
theorem restore_two (tree : BorrowTree) (completion : Completion) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (child parent source : UniIndex) (childNode parentNode : TreeNode) (lower upper : UInt64)
    (childEdge : completion.parents[child.toNat]?=some (some parent))
    (parentEdge : completion.parents[parent.toNat]?=some (some source))
    (childAt : tree.nodes.get child=some childNode) (parentAt : tree.nodes.get parent=some parentNode)
    (member : (allocation,childNode.tag)∈frame.protectedTags.toList)
    (parentUnheld : global.protectedTags.contains parentNode.tag=false)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags child) lower upper tree.locations) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion (global.endCall frame).protectedTags source) lower upper tree.locations := by
  have parentOwned:=S05CompletedChildReanchor.owned_end_call tree completion global frame allocation child parent childNode lower upper
    childEdge childAt member owned
  have unheld : (global.endCall frame).protectedTags.contains parentNode.tag=false:=by
    cases held : (global.endCall frame).protectedTags.contains parentNode.tag with
    | false=>rfl
    | true=>
      have before:=GeneralBorrowRelease.end_call_weakens global frame parentNode.tag held
      rw [parentUnheld] at before
      cases before
  exact owned_unheld_parent tree completion _ parent source parentNode lower upper parentEdge parentAt unheld parentOwned
variable {options limits remaining span before tracker data owner id} {offset len : UInt64}
    (window : UniformWindow before tracker data owner id offset.toNat len.toNat .mut)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (caller : CompilerFrameContext.ActualFrame)
    (base : UInt64) (parentTag : BorTag) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : Miri.MIR.LocalId)<caller.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span window entry caller base parentTag fresh valid15)

def completion : Completion:=S05ConcreteProtectedChildCompletion.extend window.precise.completion seed.childIndex window.pointer.grant
 def pointer : PointerInstance:=CurrentCallResourceFnEntry.child_pointer window seed.output.tag seed.childIndex

private theorem present_of_live (machine : DuplicatePrefixCallSpecification.Before) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) : Present (ActualWorld machine) id entry.allocation:=by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩

theorem present : Present (ActualWorld seed.machine) id (window.allocation.setExtra seed.output.child.tree):=by
  have actual:=present_of_live seed.machine id {entry with allocation:=entry.allocation.setExtra seed.output.child.tree} seed.live
  rw [←seed.allocationEq] at actual
  exact actual

theorem issued : SpatialDelegation seed.machine {tracker with global:=seed.output.global} id
    (window.allocation.setExtra seed.output.child.tree) (completion window entry caller base parentTag fresh valid15 seed) seed.childIndex:=by
  have both:=CurrentCallBorrowIssuance.post (CurrentCallResourceAsMutCall.accountedWindow options remaining span window)
    seed.beforeRuntime seed.output seed.childIndex offset len seed.witness seed.tag seed.machine {tracker with global:=seed.output.global}
    (present window entry caller base parentTag fresh valid15 seed) (by rw [seed.global];rfl)
  exact both.2

private def viewData : Identities:={data with interpretation:={data.interpretation with
  pointers:=data.interpretation.pointers.push (pointer window entry caller base parentTag fresh valid15 seed)
  loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,some owner,window.loan.depth+1⟩
  precise:=data.interpretation.precise.push (id,{window.precise with completion:=completion window entry caller base parentTag fresh valid15 seed})}}

/-- This appended dictionary is a technical actual child view; its array index
is not a claim of a fresh content owner or a whole CurrentDenotation. -/
private def view : UniformWindow seed.machine {tracker with global:=seed.output.global}
    (viewData window entry caller base parentTag fresh valid15 seed) data.interpretation.loans.size id offset.toNat len.toNat .mut where
  loan:=⟨data.interpretation.pointers.size,some owner,window.loan.depth+1⟩
  pointer:=pointer window entry caller base parentTag fresh valid15 seed
  allocation:=window.allocation.setExtra seed.output.child.tree
  precise:={window.precise with completion:=completion window entry caller base parentTag fresh valid15 seed}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=rfl
  present:=present window entry caller base parentTag fresh valid15 seed
  preciseAt:=by simp [viewData]
  binding:=seed.witness.binding
  issued:=issued window entry caller base parentTag fresh valid15 seed
  parents:=seed.witness.parents
  window:=seed.witness.window

theorem current : ∃ nextData nextOwner,
    ∃ child : UniformWindow seed.machine {tracker with global:=seed.output.global} nextData nextOwner id offset.toNat len.toNat .mut,
      child.pointer=pointer window entry caller base parentTag fresh valid15 seed ∧
      child.allocation=window.allocation.setExtra seed.output.child.tree ∧
      child.precise.completion=completion window entry caller base parentTag fresh valid15 seed:=
  ⟨viewData window entry caller base parentTag fresh valid15 seed,data.interpretation.loans.size,
    view window entry caller base parentTag fresh valid15 seed,rfl,rfl,rfl⟩

/-- The actual mutable helper release is derived from its SAME selected
borrow witness, with no operation-success premise. -/
theorem release :
    let result:=seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags
    result.status=.Released ∧
    result.tree={seed.output.child.tree with locations:=result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree seed.output.global ∧
    ParentInterpretation result.tree (completion window entry caller base parentTag fresh valid15 seed) ∧
    result.tree.locations.size=seed.output.child.tree.locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree (completion window entry caller base parentTag fresh valid15 seed)
      seed.output.global.protectedTags seed.childIndex) offset (offset+len) result.tree.locations := by
  obtain ⟨childData,childOwner,child,childPointer,allocationEq,completionEq⟩:=current window entry caller base parentTag fresh valid15 seed
  have treeEq : child.allocation.extra=seed.output.child.tree:=by rw [allocationEq];rfl
  have grant : child.pointer.grant=seed.childIndex:=by rw [childPointer];rfl
  obtain ⟨node,nodeAt,nodeTag,hidden⟩:=seed.hidden
  have present : child.allocation.extra.nodes.get child.pointer.grant=some node:=by rw [treeEq,grant];exact nodeAt
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts child.allocation.extra seed.output.global:=by rw [treeEq];exact seed.witness.runtime
  have concrete : ∃ supplied tag,child.pointer.value.provenance=.concrete supplied tag:=⟨id,seed.output.tag,by rw [childPointer];rfl⟩
  have sumSmall : offset.toNat+len.toNat<2^64:=by
    have bound:=seed.bounds
    have limit:=seed.output.child.tree.locations.size.bytes.toNat_lt
    omega
  have noWrap : (offset+len).toNat=offset.toNat+len.toNat:=by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt sumSmall]
  have positive : offset.toNat<(offset+len).toNat:=by
    rw [noWrap]
    have nonzero:=UInt64.lt_iff_toNat_lt.mp seed.positive
    simp only [UInt64.toNat_zero] at nonzero
    omega
  obtain ⟨done,frame,runtimeAfter,parents,capacity,owned⟩:=CurrentCallResourceRelease.release child rfl runtime concrete
    (by rw [treeEq];exact seed.distinct) (by rw [treeEq];exact seed.short) node present hidden
    offset len rfl rfl positive noWrap (by rw [treeEq,grant];exact seed.activity)
  simp only [treeEq,grant,nodeTag,completionEq] at done frame runtimeAfter parents capacity owned
  exact ⟨done,frame,runtimeAfter,parents,capacity,owned⟩

def releasedTree : BorrowTree:=(seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree
 def held : MachineHooks.BorrowState:={tracker with global:=seed.output.global}
 def postTracker : MachineHooks.BorrowState:={tracker with global:=seed.output.global.endCall seed.output.frame}

private theorem authority_weaken (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (before after : ProtectedTags) (grant : UniIndex)
    (weaken : ∀tag,after.contains tag=true→before.contains tag=true)
    (old : S05CompletedAncestryReadMutable.Authority tree completion before grant location) :
    S05CompletedAncestryReadMutable.Authority tree completion after grant location := by
  intro index node present
  have prior:=old index node present
  constructor
  · intro below
    have rights:=prior.1 below
    exact ⟨rights.1,rights.2.1,rights.2.2.1,fun active=>rights.2.2.2 (weaken node.tag active)⟩
  · intro outside
    have rights:=prior.2 outside
    exact ⟨rights.1,fun active=>rights.2 (weaken node.tag active)⟩

theorem runtime_end_call : DuplicatePrefixBorrowContract.RuntimeFacts
    (releasedTree window entry caller base parentTag fresh valid15 seed)
    (postTracker window entry caller base parentTag fresh valid15 seed).global := by
  obtain ⟨_,frame,runtime,_,_,_⟩:=release window entry caller base parentTag fresh valid15 seed
  obtain ⟨node,nodeAt,nodeTag,hidden⟩:=seed.hidden
  have childAt : (releasedTree window entry caller base parentTag fresh valid15 seed).nodes.get seed.childIndex=some node:=by
    change (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree.nodes.get seed.childIndex=some node
    rw [frame];exact nodeAt
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame (releasedTree window entry caller base parentTag fresh valid15 seed) seed.output.frame:=by
    intro row member index current present sameTag
    rw [seed.frameOwned] at member
    change row∈[(id,seed.output.tag)] at member
    have sameRow : row=(id,seed.output.tag):=List.mem_singleton.mp member
    subst row
    have one:=runtime.formed.allocator.nodeTags index current present
    have two:=runtime.formed.allocator.nodeTags seed.childIndex node childAt
    rw [sameTag] at one
    rw [nodeTag] at two
    have same : index=seed.childIndex:=Option.some.inj (one.symm.trans two)
    subst index
    have sameNode : current=node:=Option.some.inj (present.symm.trans childAt)
    subst current
    exact hidden
  exact S05CompletedChildReanchor.runtime_end_call _ seed.output.global seed.output.frame runtime hiddenFrame

theorem owned_end_call : OwnedOn (S05CompletedAncestryReadMutable.Authority
    (releasedTree window entry caller base parentTag fresh valid15 seed) (completion window entry caller base parentTag fresh valid15 seed)
    (postTracker window entry caller base parentTag fresh valid15 seed).global.protectedTags seed.childIndex)
    offset (offset+len) (releasedTree window entry caller base parentTag fresh valid15 seed).locations := by
  have owned:=(release window entry caller base parentTag fresh valid15 seed).2.2.2.2.2
  intro cursor valid positive start stop
  exact authority_weaken _ _ _ seed.output.global.protectedTags (seed.output.global.endCall seed.output.frame).protectedTags seed.childIndex
    (GeneralBorrowRelease.end_call_weakens seed.output.global seed.output.frame) (owned cursor valid positive start stop)

def value : Scalar Provenance:=Scalar.fromPointer
  (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
  (Pointer.new (.concrete id seed.output.tag) (Size.ofBytes (base+offset)))

structure Returned where
  root : CompilerFrameContext.ActualFrame
  machine : DuplicatePrefixCallSpecification.Before
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] caller before) (Storage.withCurrent #[] root machine)
  rootEq : root={AsMutPtrReturn.writeFrame (AsMutUncachedCall.cachedCaller caller valid15) 15
    (.scalar (value window entry caller base parentTag fresh valid15 seed)) seed.callerValid with location:=.mir ⟨7,0⟩}
  memory : machine.memory=RetagEntry.updatedMemory before.memory id entry (releasedTree window entry caller base parentTag fresh valid15 seed)
  tracked : machine.borrowTracker=some (postTracker window entry caller base parentTag fresh valid15 seed)
  flags : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span seed.machine machine
  active : ∃ thread,machine.threads.activeThread?=some thread ∧thread.topUserRelevantFrame=some 0
  sourceLive : machine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed)})

private theorem released_pair (result : BorrowTree.ProtectorReleaseResult) (done : result.status=.Released) :
    result=⟨result.tree,.Released⟩ := by
  cases result
  cases done
  rfl

/-- Execute the actual mutable helper's release, whole-frame endCall and pop,
returning its raw child pointer to the SAME caller at root7. -/
theorem invoke (debug : options.place.debugAssertions=false) (fuel : Nat) (validation : options.limits.validation=fuel+1) :
    Nonempty (Returned window entry caller base parentTag fresh valid15 seed) := by
  have complete : seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags=
      ⟨releasedTree window entry caller base parentTag fresh valid15 seed,.Released⟩:=
    released_pair _ (release window entry caller base parentTag fresh valid15 seed).1
  obtain ⟨root,post,step,rootEq,memory,tracked,flags,active⟩:=AsMutReturnFromReleaseRuntime.step
    options limits remaining span debug fuel validation #[] (AsMutUncachedCall.cachedCaller caller valid15)
    seed.helper seed.machine (value window entry caller base parentTag fresh valid15 seed)
    seed.body seed.size seed.argument seed.argumentAt seed.dead2 seed.dead3 seed.dead4 seed.runtime seed.location
    seed.returned seed.clocks seed.destination seed.continuation seed.varargs seed.callerValid seed.callerLive seed.callerCached seed.callerClocks
    id seed.output.tag entry seed.output.child.tree (releasedTree window entry caller base parentTag fresh valid15 seed) before.memory seed.memory
    (held window entry caller base parentTag fresh valid15 seed) seed.output.frame seed.tracked seed.borrow seed.frameOwned complete seed.cache
    seed.runtime.race seed.runtime.ghost seed.runtime.shallow
  refine ⟨{
    root:=root,machine:=post,trace:=SuccessfulTrace.append seed.trace (.next step (.refl _)),rootEq:=rootEq,
    memory:=memory,tracked:=tracked,flags:=flags,active:=active rfl,sourceLive:=?_}⟩
  rw [memory]
  exact StackPopRelease.lookup_commit_same before.memory id entry _

variable (result : Returned window entry caller base parentTag fresh valid15 seed)

theorem post_present : Present (ActualWorld result.machine) id
    (window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed)):=by
  have actual:=present_of_live result.machine id {entry with allocation:=entry.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed)} result.sourceLive
  rw [←seed.allocationEq] at actual
  exact actual

theorem post_issued : SpatialDelegation result.machine (postTracker window entry caller base parentTag fresh valid15 seed) id
    (window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed))
    (completion window entry caller base parentTag fresh valid15 seed) seed.childIndex := by
  have frame:=(release window entry caller base parentTag fresh valid15 seed).2.1
  have capacity:=(release window entry caller base parentTag fresh valid15 seed).2.2.2.2.1
  apply CurrentCallAllocationLicense.spatial (issued window entry caller base parentTag fresh valid15 seed) result.machine
    (postTracker window entry caller base parentTag fresh valid15 seed) _ (post_present window entry caller base parentTag fresh valid15 seed result)
    rfl rfl rfl capacity
  · intro position root found
    change (releasedTree window entry caller base parentTag fresh valid15 seed).roots[position]?=some root
    rw [releasedTree,frame];exact found
  · intro index node found
    refine ⟨node,?_,rfl,rfl,rfl,rfl⟩
    change (releasedTree window entry caller base parentTag fresh valid15 seed).nodes.get index=some node
    rw [releasedTree,frame];exact found
  · intro root origin edge
    exact edge

theorem post_binding : PointerBinds (window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed))
    (pointer window entry caller base parentTag fresh valid15 seed) := by
  obtain ⟨node,nodeAt,mapped,provenance⟩:=seed.witness.binding
  have frame:=(release window entry caller base parentTag fresh valid15 seed).2.1
  refine ⟨node,?_,?_,provenance⟩
  · change (releasedTree window entry caller base parentTag fresh valid15 seed).nodes.get seed.childIndex=some node
    rw [releasedTree,frame];exact nodeAt
  · change (releasedTree window entry caller base parentTag fresh valid15 seed).tagMapping.get node.tag=some seed.childIndex
    rw [releasedTree,frame];exact mapped

private theorem local_token (state : LocationState) (guarded : Bool)
    (realized : CandidateCurrentGrantResources.Realized state guarded) (right : OrdinaryBorrowAuthority.LocalWrite state guarded) :
    .exclusive∈CandidateCurrentGrantResources.tokens (CandidateCurrentGrantResources.denote state guarded) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted=>cases conflicted <;>cases accessed <;>cases guarded <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,CandidateCurrentGrantResources.Realized,CandidateCurrentGrantResources.WellFormed,
        CandidateCurrentGrantResources.denote,CandidateCurrentGrantResources.tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled=>cases accessed <;>cases guarded <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,CandidateCurrentGrantResources.Realized,CandidateCurrentGrantResources.WellFormed,
        CandidateCurrentGrantResources.denote,CandidateCurrentGrantResources.tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (guarded : Bool)
    (realized : CandidateCurrentGrantResources.Realized state guarded) (right : OrdinaryBorrowAuthority.ForeignWrite state guarded) :
    ¬CandidateCurrentGrantResources.Clash (CandidateCurrentGrantResources.guard (CandidateCurrentGrantResources.denote state guarded)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted=>cases conflicted <;>cases accessed <;>cases guarded <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,CandidateCurrentGrantResources.Realized,CandidateCurrentGrantResources.WellFormed,
        CandidateCurrentGrantResources.denote,CandidateCurrentGrantResources.guard,CandidateCurrentGrantResources.Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled=>cases accessed <;>cases guarded <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,CandidateCurrentGrantResources.Realized,CandidateCurrentGrantResources.WellFormed,
        CandidateCurrentGrantResources.denote,CandidateCurrentGrantResources.guard,CandidateCurrentGrantResources.Clash,LocationState.possible,Permission.isUnique]

theorem post_window (byte : CandidateFreezeContentResources.Byte) (inside : Window id offset.toNat len.toNat byte) :
    byte.2<(window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed)).len ∧
    CandidateCurrentGrantResources.Embeds (window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed))
      (postTracker window entry caller base parentTag fresh valid15 seed).global.protectedTags
      (completion window entry caller base parentTag fresh valid15 seed) seed.childIndex byte.2 .exclusive:=by
  have bound:=seed.bounds
  have limit:=seed.output.child.tree.locations.size.bytes.toNat_lt
  have nowrap : (offset+len).toNat=offset.toNat+len.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : offset.toNat+len.toNat<2^64)]
  refine ⟨(window.window byte inside).1,?_⟩
  intro segment member lower upper index node present
  dsimp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper present
  obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have interval:=inside.2
  have owned:=owned_end_call window entry caller base parentTag fresh valid15 seed
  have rights:=owned position valid (by have positive:=UInt64.lt_iff_toNat_lt.mp seed.positive;rw [nowrap];simp only [UInt64.toNat_zero] at positive;omega)
    (by omega) (by omega) index node present
  have runtime:=runtime_end_call window entry caller base parentTag fresh valid15 seed
  have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node present)
    ((runtime.formed.profile position valid).present index node present)
  exact ⟨fun below=>local_token _ _ realized (rights.1 below),fun clash=>Classical.byContradiction (fun outside=>foreign_no_clash _ _ realized (rights.2 outside) clash)⟩

private def postView : UniformWindow result.machine (postTracker window entry caller base parentTag fresh valid15 seed)
    (viewData window entry caller base parentTag fresh valid15 seed) data.interpretation.loans.size id offset.toNat len.toNat .mut where
  loan:=⟨data.interpretation.pointers.size,some owner,window.loan.depth+1⟩
  pointer:=pointer window entry caller base parentTag fresh valid15 seed
  allocation:=window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed)
  precise:={window.precise with completion:=completion window entry caller base parentTag fresh valid15 seed}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=rfl
  present:=post_present window entry caller base parentTag fresh valid15 seed result
  preciseAt:=by simp [viewData]
  binding:=post_binding window entry caller base parentTag fresh valid15 seed
  issued:=post_issued window entry caller base parentTag fresh valid15 seed result
  parents:=(release window entry caller base parentTag fresh valid15 seed).2.2.2.1
  window:=post_window window entry caller base parentTag fresh valid15 seed

/-- The returned raw child family is licensed in the actual root7 world after
its Strong protector ended; no whole interpretation or owner freshness is asserted. -/
theorem current_post : ∃ nextData nextOwner,
    ∃ child : UniformWindow result.machine (postTracker window entry caller base parentTag fresh valid15 seed) nextData nextOwner id offset.toNat len.toNat .mut,
      child.pointer=pointer window entry caller base parentTag fresh valid15 seed ∧
      child.allocation=window.allocation.setExtra (releasedTree window entry caller base parentTag fresh valid15 seed) ∧
      child.precise.completion=completion window entry caller base parentTag fresh valid15 seed:=
  ⟨viewData window entry caller base parentTag fresh valid15 seed,data.interpretation.loans.size,
    postView window entry caller base parentTag fresh valid15 seed result,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallResourceAsMutReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAsMutReturn" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual mutable helper return dependency {dependency}"
