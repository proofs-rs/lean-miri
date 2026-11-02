import duplicate_prefix.CurrentCallEmptyLiveBodyControl
import duplicate_prefix.CurrentCallEmptyLiveHelperGlobal
import duplicate_prefix.CurrentCallEmptyLiveHelperCurrent
import duplicate_prefix.CurrentCallEmptyLiveReturn
namespace DuplicatePrefix.CurrentCallEmptyLiveSameNonzeroFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- Actual positive-count continuation for a live empty source sharing the
Bool allocation. Its dormant zero node is released after both real helpers;
no source byte permission is required. -/
theorem finish {initial oldTracker oldData oldOwner boolId boolOffset machine tracker data owner}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance)
    (original : UniformWindow initial oldTracker oldData oldOwner boolId boolOffset 1 .ret)
    (B : UniformWindow machine tracker data owner boolId boolOffset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (sameId : physical.id=boolId) (sameOffset : physical.offset.toNat=boolOffset)
    (samePointer : physical.pointer=original.pointer.value) (sameAllocation : physical.entry.allocation=B.allocation)
    (parentIssued : SpatialDelegation machine tracker boolId B.allocation B.precise.completion original.pointer.grant)
    (parentBinding : PointerBinds B.allocation original.pointer)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (room : B.allocation.extra.nodes.size+2<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node)
    (hidden : node.isExposed=false)
    (activeB : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write physical.offset (physical.offset+1))
    (sourceTag : BorTag) (sourceIndex : UniIndex) (sourceNode : TreeNode)
    (sourceTagged : B.allocation.extra.indexOfTag sourceTag=some sourceIndex)
    (sourceAt : B.allocation.extra.nodeAt sourceIndex=some sourceNode) (sourceNodeTag : sourceNode.tag=sourceTag)
    (sourceHidden : sourceNode.isExposed=false) (quiet : S04ReturnReleaseInactive.Quiescent B.allocation.extra sourceIndex)
    (older : sourceTag.value.toNat<node.tag.value.toNat)
    (base sourceOffset count : UInt64) (nonzero : base+sourceOffset≠0) (countNonzero : count≠0)
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==boolId)=some ⟨boolId,base⟩)
    (root : RootFrame) (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (frame : CompilerFrameContext.ActualFrame)
    (installed : frame=PositiveRootInstalledFrame.installed root
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete boolId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
      count {} boolId sourceTag boolId node.tag)
    (rootStop : root.frame.returnContinuation=.stop true)
    (rootDestination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (rootVarargs : root.frame.vaList=#[])
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (enabled : machine.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (threadAt : machine.threads.activeThread?=some thread) (topZero : thread.topUserRelevantFrame=some 0)
    (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original.pointer.grant))
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (dynamicFuel fuel budget : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (fuelEq : options.limits.validation=fuel+1) (dispatchEq : limits.callDispatch=budget+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  let entry:={physical.entry with allocation:=B.allocation}
  have entryEq : entry=physical.entry := by dsimp only [entry];rw [←sameAllocation]
  have live : machine.memory.live.find? (fun row=>row.1==boolId)=some (boolId,entry) := by
    rw [entryEq,←sameId];exact physical.live
  have fresh : tracker.global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have nodeRoom : B.allocation.extra.nodes.size+2≤4294967295 := by omega
  let first:=CurrentCallEmptyLiveBodyControl.sourceInput B.allocation.extra tracker.global runtime sourceTag sourceIndex sourceNode sourceTagged sourceAt nodeRoom
  let second:=S03EmptyNextLenInput.form B.allocation.extra tracker.global runtime sourceTag first fresh nodeRoom
  obtain ⟨result,post,tree,next,treeEq,traceBefore,body,identity,callee,extra,returnPlace,continuation,varargs,_,size,located,slot0,immediate,
    postLive,memory,enabledNow,modeEq,⟨nextFresh,nextEq⟩,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,⟨finalThread,activeNow⟩⟩:=
    CurrentCallEmptyLiveBodyControl.to_return options limits remaining span root raw machine tracker enabled model origins sourceTag boolId entry sourceIndex sourceNode
      sourceTagged sourceAt runtime base sourceOffset count nonzero countNonzero cached live boolId node.tag frame installed fresh tagRoom nodeRoom
      dynamicFuel fuel budget dynamicEq fuelEq dispatchEq thread threadAt topZero
  have finalTree : tree=second.after:=treeEq
  have globalFacts:=CurrentCallEmptyLiveHelperGlobal.facts B.allocation.extra tracker runtime fresh nextFresh boolId
  rw [←nextEq] at globalFacts
  obtain ⟨globalShape,nextNat,_⟩:=globalFacts
  have postPresent : Present (ActualWorld post) boolId (B.allocation.setExtra second.after) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(boolId,{entry with allocation:=entry.allocation.setExtra tree}),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some postLive),?_⟩
    rw [finalTree]
  obtain ⟨nextData,Q,pointerQ,loanQ,allocationQ,completionQ,parentBindingQ,parentIssuedQ⟩:=CurrentCallEmptyLiveHelperCurrent.window B runtime sourceTag first fresh nodeRoom
    post next globalShape nextNat postPresent original.pointer parentBinding parentIssued physical.offset sameOffset
  have firstDifferent : B.pointer.grant≠first.parent := by
    change B.pointer.grant≠sourceIndex
    intro same
    have sameNode : node=sourceNode:=Option.some.inj (nodeAt.symm.trans (by rw [same];exact sourceAt))
    rw [sameNode,sourceNodeTag] at older
    omega
  have secondDifferent : B.pointer.grant≠second.parent := by
    change B.pointer.grant≠first.index
    intro same
    rw [same,first.vacant] at nodeAt
    cases nodeAt
  obtain ⟨⟨nextNode,nextAt,nextTag,nextParent,nextChildren,nextHidden⟩,nextActive,nextTagged,⟨nextSource,nextSourceAt,nextSourceTag,nextSourceParent,nextSourceHidden⟩,nextQuiet⟩:=
    CurrentCallEmptyLiveHelperFacets.two B.allocation.extra sourceTag tracker.global.nextPointerTag first tracker.global.nextPointerTag
      (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) second B.pointer.grant node nodeAt firstDifferent secondDifferent
      physical.offset (physical.offset+1) activeB sourceIndex sourceTag sourceNode sourceTagged sourceAt sourceHidden quiet
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts second.after next.global := by
    -- The window's parent interpretation supplies geometry; runtime follows
    -- the actual two zero constructors under the restored protector table.
    have flags : next.global.protectedTags=tracker.global.protectedTags:=by rw [globalShape]
    have initialRuntime:=CurrentCallZeroSharedBoolWindow.runtime_mono B.allocation.extra tracker.global next.global runtime flags (by omega)
    have firstBound : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat:=by omega
    have afterFirst:=S03EmptySharedRuntime.construct B.allocation.extra next.global initialRuntime sourceTag tracker.global.nextPointerTag first (by omega) firstBound
    exact S03EmptySharedRuntime.construct first.after next.global afterFirst tracker.global.nextPointerTag
      (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) second
      (by
        have growth:=EmptyForestSharedPoolNext.node_size first
        have bound : EmptyForestSharedPoolNext.growth first≤1 := by
          cases s:first.slot <;> simp [EmptyForestSharedPoolNext.growth,s]
        omega)
      (by rw [GenericFunctionEntryNumerics.successor_value];omega)
  obtain ⟨P,pointerP,idP,offsetP,bindingP⟩:=CurrentCallRootPhysicalWindow.tree_update physical binding boolId entry tree live addresses
    (by rw [memory];rfl)
  have liveP : post.memory.live.find? (fun row=>row.1==boolId)=some (boolId,P.entry) := by rw [←sameId,←idP];exact P.live
  have finalEntryEq : P.entry={entry with allocation:=entry.allocation.setExtra tree}:=
    (Prod.mk.inj (Option.some.inj (liveP.symm.trans postLive))).2
  have allocationP : P.entry.allocation=Q.allocation := by rw [finalEntryEq,allocationQ,finalTree]
  have roots : Q.allocation.extra.roots.toList.Nodup := by
    rw [allocationQ,show (B.allocation.setExtra second.after).extra=second.after from rfl,S03EmptyPositiveTreeFacts.roots runtime sourceTag first fresh nodeRoom]
    exact distinct
  have short : Q.allocation.extra.nodes.size<65536 := by
    rw [allocationQ]
    have growth:=S03EmptyPositiveTreeFacts.size runtime sourceTag first fresh nodeRoom
    change second.after.nodes.size<65536
    change second.after.nodes.size≤B.allocation.extra.nodes.size+2 at growth
    omega
  have nodeQ : Q.allocation.extra.nodes.get Q.pointer.grant=some nextNode := by rw [allocationQ,pointerQ];exact nextAt
  have hiddenQ : nextNode.isExposed=false:=nextHidden.trans hidden
  have quietEntry : S04ReturnReleaseInactive.Quiescent ({entry with allocation:=entry.allocation.setExtra tree}).allocation.extra sourceIndex := by
    change S04ReturnReleaseInactive.Quiescent tree sourceIndex
    rw [finalTree];exact nextQuiet
  have hiddenOnBool : ∀index current,Q.allocation.extra.nodes.get index=some current→current.tag=sourceTag→current.isExposed=false := by
    intro index current found tagged
    rw [allocationQ] at found
    have indexTagged:=nextRuntime.formed.allocator.nodeTags index current found
    rw [tagged] at indexTagged
    have same : index=sourceIndex:=Option.some.inj (indexTagged.symm.trans nextTagged)
    subst index
    have equal : current=nextSource:=Option.some.inj (found.symm.trans nextSourceAt)
    rw [equal];exact nextSourceHidden
  have edgeQ : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some original.pointer.grant) := by
    rw [completionQ,pointerQ]
    have oldLive : ∃n,B.allocation.extra.nodes.get B.pointer.grant=some n:=⟨node,nodeAt⟩
    have firstDifferentChild : B.pointer.grant≠first.index:=by intro same;rw [same,first.vacant] at nodeAt;cases nodeAt
    have secondDifferentChild : B.pointer.grant≠second.index := by
      obtain ⟨middle,middleAt,_⟩:=S03EmptySharedFrame.old_node first B.pointer.grant node nodeAt
      change first.after.nodes.get B.pointer.grant=some middle at middleAt
      intro same
      rw [same,second.vacant] at middleAt
      cases middleAt
    have firstOld:=S05ConcreteProtectedChildCompletion.old_parent B.precise.completion first.index first.parent B.pointer.grant firstDifferentChild (Array.getElem?_eq_some_iff.mp edge).1
    have firstEdge:=firstOld.trans edge
    exact (S05ConcreteProtectedChildCompletion.old_parent (S05ConcreteProtectedChildCompletion.extend B.precise.completion first.index first.parent)
      second.index second.parent B.pointer.grant secondDifferentChild (Array.getElem?_eq_some_iff.mp firstEdge).1).trans firstEdge
  have metadata:=PositiveRootInstalledFrame.metadata root
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete boolId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm count {} boolId sourceTag boolId node.tag
  rw [←installed] at metadata
  let borrowFrame:FrameState:=(({}:FrameState).addProtector boolId sourceTag).addProtector boolId node.tag
  have tags : borrowFrame.protectedTags=#[(boolId,sourceTag),(boolId,nextNode.tag)] := by rw [nextTag];rfl
  have trackedFrame : result.extra.borrowTracker=some borrowFrame := by rw [extra];exact metadata.2.2.2.2.2.2.2.1
  have finalMode : next.retagMode=.Default := by
    obtain ⟨old,tracked,default⟩:=model.defaultTracker
    have same : old=tracker:=Option.some.inj (tracked.symm.trans enabled)
    subst old
    exact modeEq.trans default
  have finalModel : DuplicatePrefixCallModel.Model options remaining span post :=
    ⟨model.debugOff,model.preciseOff,model.implicitOff,ghost,shallow,⟨next,enabledNow,finalMode⟩,race,backend.trans model.noBackend,
      by rw [types];exact model.metadata,fixed,unchecked,noGc,model.nullComparator,model.sourceMatches⟩
  obtain ⟨final,returned,terminal,emptyStack⟩:=CurrentCallEmptyLiveReturn.finish options limits remaining span place original Q P bindingP
    (idP.trans sameId) ((congrArg UInt64.toNat offsetP).trans sameOffset) (pointerP.trans samePointer) allocationP parentIssuedQ parentBindingQ
    (by rw [allocationQ];exact nextRuntime) roots short (by rw [pointerQ];exact concrete) nextNode nodeQ hiddenQ
    (by rw [allocationQ,pointerQ,offsetP];exact nextActive)
    boolId sourceTag {entry with allocation:=entry.allocation.setExtra tree} postLive sourceIndex nextSource
    (by change tree.indexOfTag sourceTag=some sourceIndex;rw [finalTree];exact nextTagged)
    (by change tree.nodeAt sourceIndex=some nextSource;rw [finalTree];exact nextSourceAt) nextSourceHidden quietEntry hiddenOnBool result borrowFrame tags trackedFrame
    (body.trans (metadata.1.trans root.body)) located size (by rw [extra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks)
    (continuation.trans (metadata.2.2.2.1.trans rootStop)) (varargs.trans (metadata.2.2.2.2.2.1.trans rootVarargs)) immediate false slot0
    (by rw [returnPlace,metadata.2.2.2.2.1];exact rootDestination) finalModel enabledNow finalThread activeNow edgeQ
    (by rw [idP,offsetP];exact ready.transport extras) fuel fuelEq
  exact ⟨final,SuccessfulTrace.append traceBefore returned,terminal,emptyStack⟩
end
end DuplicatePrefix.CurrentCallEmptyLiveSameNonzeroFinish
