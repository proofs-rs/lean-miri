import duplicate_prefix.GeneralBorrowScopedWindowLenTargetActivity
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowFnEntryActivity
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowNonzeroLenWindow
import duplicate_prefix.GeneralBorrowScopedWindowWritableLenTargetMetadata
import duplicate_prefix.GeneralBorrowScopedWindowDualDataReturnPlan
import duplicate_prefix.GeneralBorrowScopedDualRootRejectedPhysical
import duplicate_prefix.GeneralBorrowScopedRejectedFrameReady
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowRejected
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowPositiveWildcardWindowNonzeroInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure Initial extends GeneralBorrowPositiveWildcardWindowNonzeroInput.Initial where
  rejected : count>len/2

private theorem inserted_removed_other (tags : ProtectedTags) (tag query : BorTag) (different : query≠tag) :
    ((tags.insert tag .StrongProtector).remove tag).contains query=tags.contains query := by
  simp only [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.remove_other _ tag query different,
    GeneralBorrowProtectorCacheMap.insert_other _ tag query .StrongProtector different]
private theorem inserted_removed_free (tags : ProtectedTags) (tag query : BorTag) (free : tags.contains query=false) :
    ((tags.insert tag .StrongProtector).remove tag).contains query=false := by
  by_cases same : query=tag
  · subst query;simp [ProtectedTags.contains]
  · rw [inserted_removed_other tags tag query same];exact free
private theorem cell_eq (row : LocalState Provenance LocalLayout) (value : LocalValue Provenance) (layout : Option LocalLayout)
    (v : row.value=value) (l : row.layout=layout) : row=⟨value,layout⟩ := by
  cases row;cases v;cases l;rfl
private theorem row_at (frame : CompilerFrameContext.ActualFrame) (index : Nat) (valid : index<frame.locals.size)
    (row : LocalState Provenance LocalLayout) (known : frame.locals[index]?=some row) : frame.locals[index]'valid=row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)

/-- The original wildcard caller, real shared/len prefix and rejected guard
form the physical false-return input internally, including both callback kinds. -/
theorem prepare (s : Initial) :
    ∃ (input : GeneralBorrowScopedDualRootRejectedPhysical.Input),∃ installed,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed (Storage.withCurrent #[] input.before input.machine) := by
  obtain ⟨updated,callInput,installed,origin,call,root,post,released,prefixTrace,rootEq,memoryEq,trackerEq,complete,uniqueData,
    well,size,runtime,rootRuntime,found,nodeTags,context,writeData,coherent,readData,writableData⟩:=GeneralBorrowPositiveWildcardWindowNonzeroLenWindow.invoke s.toInitial
  let oldHeld:=GeneralBorrowScopedWindowWritableLenTargetMetadata.held callInput
  let helperFrame:=({}:FrameState).addProtector callInput.id callInput.tracker.global.nextPointerTag
  let tracker : MachineHooks.BorrowState := {oldHeld with global:=oldHeld.global.endCall helperFrame}
  have sourceEq : GeneralBorrowScopedWindowWritableLenTargetMetadata.tree callInput=released := by
    unfold GeneralBorrowScopedWindowWritableLenTargetMetadata.tree GeneralBorrowScopedWindowWritableLenTargetMetadata.held
    rw [complete]
  have metadata:=GeneralBorrowScopedWindowWritableLenTargetMetadata.source callInput
  rw [sourceEq] at metadata
  obtain ⟨targetNode,targetPresent,targetTag,targetHidden⟩:=metadata.1
  have targetTagged : released.indexOfTag s.tracker.global.nextPointerTag=some callInput.first.parent := by
    have value : targetNode.tag=s.tracker.global.nextPointerTag:=targetTag.trans origin.parentNodeTag
    simpa only [BorrowTree.indexOfTag,value] using nodeTags callInput.first.parent targetNode targetPresent
  have contextNode : context.anchorNode=targetNode := Option.some.inj (context.anchorPresent.symm.trans targetPresent)
  have initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin callInput.first.tree callInput.first.parent .Write callInput.offset (callInput.offset+callInput.len) := by
    rw [origin.firstTree,origin.target,origin.offset,origin.len]
    exact GeneralBorrowPositiveWildcardWindowFnEntryActivity.source s.toInitial.toBase s.vacantClean
  have targetActive := GeneralBorrowScopedWindowLenTargetActivity.source callInput
    (origin.firstOffset.trans origin.offset.symm) (origin.firstLen.trans origin.len.symm) initialActive
  change GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowScopedWindowWritableLenTargetMetadata.tree callInput)
    callInput.first.parent .Write callInput.offset (callInput.offset+callInput.len) at targetActive
  rw [sourceEq] at targetActive
  have positiveWindow : callInput.offset.toNat<(callInput.offset+callInput.len).toNat := by
    simpa only [callInput.offsetEq,callInput.lenEq] using callInput.rangePositive
  have both : ∀ kind,GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
      tracker.global.protectedTags callInput.first.parent callInput.selected callInput.head callInput.tail kind)) callInput.offset (callInput.offset+callInput.len) released.locations := by
    intro kind
    cases kind with
    | Read => simpa only [tracker,oldHeld,GeneralBorrowScopedWindowWritableLenTargetMetadata.held,helperFrame] using readData
    | Write => simpa only [tracker,oldHeld,GeneralBorrowScopedWindowWritableLenTargetMetadata.held,helperFrame] using writeData
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind:={callInput.entry with allocation:=callInput.entry.allocation.setExtra released}
  let slot : LocalAllocation Provenance BorrowTree MiriMemoryKind:={s.slotEntry with allocation:=updated}
  let slotTag:=(GeneralBorrowPositiveWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
  have beforeRootFree : callInput.tracker.global.protectedTags.contains s.slotRoot=false := by
    rw [origin.tracker]
    exact GenericFunctionEntryState.buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct s.slotFree
  have rootFree : tracker.global.protectedTags.contains s.slotRoot=false := by
    change ((callInput.tracker.global.protectedTags.insert callInput.tracker.global.nextPointerTag .StrongProtector).remove callInput.tracker.global.nextPointerTag).contains s.slotRoot=false
    exact inserted_removed_free _ _ _ beforeRootFree
  have distinct : slotTag≠callInput.tracker.global.nextPointerTag := by
    rw [origin.tracker]
    have two : (held s.toInitial.toBase).global.nextPointerTag.value.toNat=slotTag.value.toNat+1 :=
      GenericFunctionEntryNumerics.successor_value slotTag s.slotFresh
    have three : (expressionTracker s.toInitial.toBase).global.nextPointerTag.value.toNat=(held s.toInitial.toBase).global.nextPointerTag.value.toNat+1 :=
      GenericFunctionEntryNumerics.successor_value (held s.toInitial.toBase).global.nextPointerTag s.sharedFresh
    intro equal
    have value:=congrArg (fun tag : BorTag=>tag.value.toNat) equal
    omega
  have slotHeld : tracker.global.protectedTags.contains slotTag=true := by
    change ((callInput.tracker.global.protectedTags.insert callInput.tracker.global.nextPointerTag .StrongProtector).remove callInput.tracker.global.nextPointerTag).contains slotTag=true
    rw [inserted_removed_other _ _ _ distinct,origin.tracker]
    exact GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh
  have slotPresent : post.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,slot) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_other callInput.beforeMachine.memory callInput.id s.slotId callInput.entry slot released
      (by rw [origin.id];exact s.separate) origin.slotPresent
  have bufferPresent : post.memory.live.find? (fun row=>row.1==s.id)=some (s.id,buffer) := by simpa only [origin.id] using found
  let release:=GeneralBorrowScopedWindowDualDataReturnPlan.build post.memory tracker.global.protectedTags s.id s.tracker.global.nextPointerTag buffer bufferPresent
    callInput.first.parent callInput.selected callInput.head callInput.tail context (by rw [contextNode];exact targetHidden) targetTagged
    callInput.offset callInput.len positiveWindow well targetActive metadata.2 both s.slotId s.separate slot slotPresent s.slotRoot slotTag
    origin.slotTree rootFree slotHeld s.slotDistinct
  let sharedValue:=(RetagReferencePlace.sliceValue (config callInput.options callInput.remaining callInput.span).access.runtime.base
    (Pointer.new (.concrete callInput.id callInput.exprTag) (Size.ofBytes (callInput.base+callInput.offset))) callInput.len SharedReferenceMetadata.sharedLayout).imm
  have preFacts : GeneralBorrowForestSharedPreLenFrame.Facts callInput.caller callInput.caller s.count sharedValue := by
    refine ⟨callInput.sourceBody,callInput.identity,callInput.callee,origin.size,callInput.located,rfl,rfl,rfl,rfl,origin.allImmediate,
      origin.slot0,origin.slot7,origin.slot8,origin.slot9,origin.slot10,?_,?_,origin.slot13⟩
    · rw [Array.getElem?_eq_getElem callInput.valid]
      exact congrArg some (cell_eq _ _ _ callInput.live callInput.uncached)
    · rw [Array.getElem?_eq_getElem callInput.sourceValid]
      exact congrArg some (cell_eq _ _ _ callInput.sourceLive callInput.sourceCached)
  have facts : GeneralBorrowScopedRejectedFrameReady.Facts callInput.caller root s.count callInput.len sharedValue := by
    rw [rootEq]
    exact GeneralBorrowScopedRejectedFrameReady.build _ _ _ _ _ preFacts callInput.valid
  have postRuntime:=rootRuntime origin.frames
  rw [origin.options,origin.remaining,origin.span] at postRuntime
  have fullRuntime:=GeneralBorrowPositiveWildcardWindowNonzeroLenWindow.runtime_trans s.options s.remaining s.span s.before callInput.beforeMachine post origin.runtime postRuntime
  obtain ⟨thread,active,cache⟩:=fullRuntime.active
  let result : GeneralBorrowScopedDualRootRejectedPhysical.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,source:=s.source,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=root,len:=callInput.len,count:=s.count,rejected:=by rw [origin.len];exact s.rejected,
    frameSize:=facts.size,location:=facts.location,all:=facts.all,temp12:=sharedValue,
    live12:=congrArg LocalState.value (row_at root 12 (by rw [facts.size];decide) _ facts.slot12),
    live13:=congrArg LocalState.value (row_at root 13 (by rw [facts.size];decide) _ facts.slot13),
    cache13:=congrArg LocalState.layout (row_at root 13 (by rw [facts.size];decide) _ facts.slot13),
    live0:=congrArg LocalState.value (row_at root 0 (by rw [facts.size];decide) _ facts.slot0),
    cache0:=congrArg LocalState.layout (row_at root 0 (by rw [facts.size];decide) _ facts.slot0),
    live7:=congrArg LocalState.value (row_at root 7 (by rw [facts.size];decide) _ facts.slot7),
    live8:=congrArg LocalState.value (row_at root 8 (by rw [facts.size];decide) _ facts.slot8),
    cache8:=congrArg LocalState.layout (row_at root 8 (by rw [facts.size];decide) _ facts.slot8),
    live9:=congrArg LocalState.value (row_at root 9 (by rw [facts.size];decide) _ facts.slot9),
    cache9:=congrArg LocalState.layout (row_at root 9 (by rw [facts.size];decide) _ facts.slot9),
    live10:=congrArg LocalState.value (row_at root 10 (by rw [facts.size];decide) _ facts.slot10),
    cache10:=congrArg LocalState.layout (row_at root 10 (by rw [facts.size];decide) _ facts.slot10),
    live11:=congrArg LocalState.value (row_at root 11 (by rw [facts.size];decide) _ facts.slot11),
    cache11:=congrArg LocalState.layout (row_at root 11 (by rw [facts.size];decide) _ facts.slot11),
    body:=facts.body,identity:=facts.identity,callee:=facts.callee,noLocalClocks:=by rw [facts.extra];exact callInput.noClocks,
    continuation:=facts.continuation.trans origin.rootContinuation,varargs:=facts.varargs.trans origin.rootVa,
    machine:=post,tracker:=tracker,tracked:=trackerEq,defaultMode:=callInput.defaultMode,noClocks:=fullRuntime.race,noBackend:=fullRuntime.backend,
    ghost:=fullRuntime.ghost,shallow:=fullRuntime.shallow,unchecked:=fullRuntime.unchecked,noGc:=fullRuntime.noGc,fixed:=fullRuntime.fixed,
    thread:=thread,active:=active,release:=release,frameTracked:=by rw [facts.extra];exact origin.frameBorrow,
    slotSize:=origin.slotSize,slotStorage:=origin.slotLen,slotMask:=origin.slotMask,slotProvenance:=origin.slotProvenance,slotMutable:=origin.slotMutable,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [fullRuntime.addresses];exact s.slotCached,
    extras:=by change post.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [fullRuntime.extras];exact s.extras,
    destination:=by rw [facts.returnPlace];exact origin.rootReturn }
  exact ⟨result,installed,rfl,rfl,rfl,rfl,call,prefixTrace⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowRejected
