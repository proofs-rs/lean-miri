import duplicate_prefix.CurrentCallEmptyLiveBodyControl
import duplicate_prefix.CurrentCallEmptyLiveHelperGlobal
import duplicate_prefix.CurrentCallEmptyLiveHelperCurrent
import duplicate_prefix.CurrentCallEmptyPointerReturn
namespace DuplicatePrefix.CurrentCallEmptyPointerDifferentFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- Actual positive-count continuation for a live empty source in a separate
allocation from Bool. Its dormant zero node is released after both real helpers;
no source byte permission is required. -/
theorem finish {boolId boolOffset machine tracker data owner}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance)
    (original : PointerInstance) (originalId : original.allocation=boolId)
    (B : UniformWindow machine tracker data owner boolId boolOffset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (sameId : physical.id=boolId) (sameOffset : physical.offset.toNat=boolOffset)
    (samePointer : physical.pointer=original.value) (sameAllocation : physical.entry.allocation=B.allocation)
    (parentIssued : SpatialDelegation machine tracker boolId B.allocation B.precise.completion original.grant)
    (parentBinding : PointerBinds B.allocation original)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (distinct : B.allocation.extra.roots.toList.Nodup) (room : B.allocation.extra.nodes.size<65536)
    (concrete : ∃ supplied tag,B.pointer.value.provenance=.concrete supplied tag)
    (node : TreeNode) (nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node)
    (hidden : node.isExposed=false)
    (activeB : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write physical.offset (physical.offset+1))
    (sourceId : AllocId) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry))
    (differentIds : sourceId≠boolId)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (sourceRoom : sourceEntry.allocation.extra.nodes.size+2≤4294967295)
    (sourceTag : BorTag) (sourceIndex : UniIndex) (sourceNode : TreeNode)
    (sourceTagged : sourceEntry.allocation.extra.indexOfTag sourceTag=some sourceIndex)
    (sourceAt : sourceEntry.allocation.extra.nodeAt sourceIndex=some sourceNode)
    (sourceHidden : sourceNode.isExposed=false) (quiet : S04ReturnReleaseInactive.Quiescent sourceEntry.allocation.extra sourceIndex)
    (sourceHiddenOnBool : ∀index current,B.allocation.extra.nodes.get index=some current→current.tag=sourceTag→current.isExposed=false)
    (base sourceOffset count : UInt64) (nonzero : base+sourceOffset≠0) (countNonzero : count≠0)
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (root : RootFrame) (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (frame : CompilerFrameContext.ActualFrame)
    (installed : frame=PositiveRootInstalledFrame.installed root
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete sourceId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
      count {} sourceId sourceTag boolId node.tag)
    (rootStop : root.frame.returnContinuation=.stop true)
    (rootDestination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (rootVarargs : root.frame.vaList=#[])
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (enabled : machine.borrowTracker=some tracker)
    (thread : Miri.Concurrency.ThreadRecord) (threadAt : machine.threads.activeThread?=some thread) (topZero : thread.topUserRelevantFrame=some 0)
    (edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some original.grant))
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (dynamicFuel fuel budget : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (fuelEq : options.limits.validation=fuel+1) (dispatchEq : limits.callDispatch=budget+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  let entry:=sourceEntry
  have live : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry):=sourceLive
  have fresh : tracker.global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2≤4294967295:=sourceRoom
  let first:=CurrentCallEmptyLiveBodyControl.sourceInput sourceEntry.allocation.extra tracker.global sourceRuntime sourceTag sourceIndex sourceNode sourceTagged sourceAt nodeRoom
  let second:=S03EmptyNextLenInput.form sourceEntry.allocation.extra tracker.global sourceRuntime sourceTag first fresh nodeRoom
  obtain ⟨result,post,tree,next,treeEq,traceBefore,body,identity,callee,extra,returnPlace,continuation,varargs,_,size,located,slot0,immediate,
    postLive,memory,enabledNow,modeEq,⟨nextFresh,nextEq⟩,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,⟨finalThread,activeNow⟩⟩:=
    CurrentCallEmptyLiveBodyControl.to_return options limits remaining span root raw machine tracker enabled model origins sourceTag sourceId entry sourceIndex sourceNode
      sourceTagged sourceAt sourceRuntime base sourceOffset count nonzero countNonzero cached live boolId node.tag frame installed fresh tagRoom nodeRoom
      dynamicFuel fuel budget dynamicEq fuelEq dispatchEq thread threadAt topZero
  have finalTree : tree=second.after:=treeEq
  have globalFacts:=CurrentCallEmptyLiveHelperGlobal.facts sourceEntry.allocation.extra tracker sourceRuntime fresh nextFresh sourceId
  rw [←nextEq] at globalFacts
  obtain ⟨globalShape,nextNat,_⟩:=globalFacts
  have boolLive : post.memory.live.find? (fun row=>row.1==boolId)=some (boolId,physical.entry) := by
    rw [memory]
    exact StackPopRelease.lookup_commit_other machine.memory sourceId boolId entry physical.entry tree (Ne.symm differentIds)
      (by rw [←sameId];exact physical.live)
  have postPresent : Present (ActualWorld post) boolId B.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    exact ⟨(boolId,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some boolLive),by rw [sameAllocation]⟩
  have parentIssuedQ:=CurrentCallAllocationLicense.spatial parentIssued post next B.allocation postPresent (by rw [globalShape];rfl)
    rfl rfl rfl (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
    B.precise.completion (by intro first second e;exact e)
  let Q : UniformWindow post next data owner boolId boolOffset 1 .ret:={B with
    present:=postPresent
    issued:=CurrentCallAllocationLicense.spatial B.issued post next B.allocation postPresent (by rw [globalShape];rfl)
      rfl rfl rfl (by intro position root found;exact found) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      B.precise.completion (by intro first second e;exact e)
    window:=by intro byte inside;obtain ⟨bound,embedding⟩:=B.window byte inside;refine ⟨bound,?_⟩;rw [globalShape];exact embedding}
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra next.global:=
    CurrentCallZeroSharedBoolWindow.runtime_mono B.allocation.extra tracker.global next.global runtime (by rw [globalShape]) (by omega)
  obtain ⟨nextSource,nextSourceAt,nextSourceTag,nextSourceParent,nextSourceHiddenEq⟩:=S03EmptyPositiveTreeFacts.old_node sourceRuntime sourceTag first fresh nodeRoom sourceIndex sourceNode sourceAt
  have nextSourceHidden : nextSource.isExposed=false:=nextSourceHiddenEq.trans sourceHidden
  have nextTagged:=S03EmptyPositiveTreeFacts.tagged sourceRuntime sourceTag first fresh nodeRoom sourceTag sourceIndex sourceTagged
  have nextQuiet:=S03EmptySharedFrame.quiescent second sourceIndex (S03EmptySharedFrame.quiescent first sourceIndex quiet)
  obtain ⟨P,pointerP,idP,offsetP,bindingP⟩:=CurrentCallRootPhysicalWindow.tree_update physical binding sourceId entry tree live addresses
    (by rw [memory];rfl)
  have liveP : post.memory.live.find? (fun row=>row.1==boolId)=some (boolId,P.entry) := by rw [←sameId,←idP];exact P.live
  have finalEntryEq : P.entry=physical.entry := (Prod.mk.inj (Option.some.inj (liveP.symm.trans boolLive))).2
  have allocationP : P.entry.allocation=Q.allocation := by rw [finalEntryEq];exact sameAllocation
  have roots : Q.allocation.extra.roots.toList.Nodup:=distinct
  have short : Q.allocation.extra.nodes.size<65536:=room
  have nodeQ : Q.allocation.extra.nodes.get Q.pointer.grant=some node:=nodeAt
  have quietEntry : S04ReturnReleaseInactive.Quiescent ({entry with allocation:=entry.allocation.setExtra tree}).allocation.extra sourceIndex := by
    change S04ReturnReleaseInactive.Quiescent tree sourceIndex
    rw [finalTree];exact nextQuiet
  have edgeQ : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some original.grant):=edge
  have metadata:=PositiveRootInstalledFrame.metadata root
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete sourceId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm count {} sourceId sourceTag boolId node.tag
  rw [←installed] at metadata
  let borrowFrame:FrameState:=(({}:FrameState).addProtector sourceId sourceTag).addProtector boolId node.tag
  have tags : borrowFrame.protectedTags=#[(sourceId,sourceTag),(boolId,node.tag)] := rfl
  have trackedFrame : result.extra.borrowTracker=some borrowFrame := by rw [extra];exact metadata.2.2.2.2.2.2.2.1
  have finalMode : next.retagMode=.Default := by
    obtain ⟨old,tracked,default⟩:=model.defaultTracker
    have same : old=tracker:=Option.some.inj (tracked.symm.trans enabled)
    subst old
    exact modeEq.trans default
  have finalModel : DuplicatePrefixCallModel.Model options remaining span post :=
    ⟨model.debugOff,model.preciseOff,model.implicitOff,ghost,shallow,⟨next,enabledNow,finalMode⟩,race,backend.trans model.noBackend,
      by rw [types];exact model.metadata,fixed,unchecked,noGc,model.nullComparator,model.sourceMatches⟩
  obtain ⟨final,returned,terminal,emptyStack⟩:=CurrentCallEmptyPointerReturn.finish options limits remaining span place original originalId Q P bindingP
    (idP.trans sameId) ((congrArg UInt64.toNat offsetP).trans sameOffset) (pointerP.trans samePointer) allocationP parentIssuedQ parentBinding
    nextRuntime roots short concrete node nodeQ hidden
    (by rw [offsetP];exact activeB)
    sourceId sourceTag {entry with allocation:=entry.allocation.setExtra tree} postLive sourceIndex nextSource
    (by change tree.indexOfTag sourceTag=some sourceIndex;rw [finalTree];exact nextTagged)
    (by change tree.nodeAt sourceIndex=some nextSource;rw [finalTree];exact nextSourceAt) nextSourceHidden quietEntry sourceHiddenOnBool result borrowFrame tags trackedFrame
    (body.trans (metadata.1.trans root.body)) located size (by rw [extra];exact metadata.2.2.2.2.2.2.1.trans root.noClocks)
    (continuation.trans (metadata.2.2.2.1.trans rootStop)) (varargs.trans (metadata.2.2.2.2.2.1.trans rootVarargs)) immediate false slot0
    (by rw [returnPlace,metadata.2.2.2.2.1];exact rootDestination) finalModel enabledNow finalThread activeNow edgeQ
    (by rw [idP,offsetP];exact ready.transport extras) fuel fuelEq
  exact ⟨final,SuccessfulTrace.append traceBefore returned,terminal,emptyStack⟩
end
end DuplicatePrefix.CurrentCallEmptyPointerDifferentFinish
