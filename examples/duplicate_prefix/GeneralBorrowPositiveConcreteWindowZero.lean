import duplicate_prefix.GeneralBorrowScopedInactiveWritableWindowDataReturnPlan
import duplicate_prefix.GeneralBorrowScopedInactiveWritableRootZeroPhysical
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAsMutRawReleaseData
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowInputGeometry
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedToShared
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowInvocationBase
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
import duplicate_prefix.GenericFunctionEntryNumerics
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFunctionRuntime
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFnEntryActivity
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowZero
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
open Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure InitialFor (profileMode : ProfileMode) extends toBase : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode where
  zero : count=0
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra

/-- Legacy global caller contract; window callers use InitialFor .window. -/
abbrev Initial := InitialFor .global

private theorem untick (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (facts : GenericSharedLenAccepted.RuntimeFacts options remaining span before (RootZeroCompleteState.tick options remaining span machine)) :
    GenericSharedLenAccepted.RuntimeFacts options remaining span before machine := by
  have data : (RootZeroCompleteState.tick options remaining span machine).user.addresses=machine.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  exact ⟨(RootZeroCompleteState.tick_ghost options remaining span machine).symm.trans facts.ghost,
    (RootZeroCompleteState.tick_shallow options remaining span machine).symm.trans facts.shallow,
    facts.race,data.1.symm.trans facts.addresses,data.2.1.symm.trans facts.types,data.2.2.1.symm.trans facts.extras,
    data.2.2.2.symm.trans facts.backend,
    (RootZeroCompleteState.tick_flags options remaining span machine).1.symm.trans facts.unchecked,
    (RootZeroCompleteState.tick_flags options remaining span machine).2.symm.trans facts.noGc,facts.fixed,facts.active⟩

/-- Original actual wildcard initStackFrame forms the zero-count scoped
return input; no post-entry Resources, callback success or release plan is an
initial assumption. -/
theorem prepare {profileMode : ProfileMode} (s : InitialFor profileMode) :
    ∃ input : GeneralBorrowScopedInactiveWritableRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowPositiveConcreteWindowInvocationBase.enters s.toBase 0
  let raw := RawRootInvocation.root s.before s.place s.race
  let rawMachine := RawRootInvocation.machine #[] s.before
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  let tag := (next s.tracker s.fresh).global.nextPointerTag
  let tracker := held s.tracker s.fresh s.slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  let machine := enteredMachine rawMachine s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
  change _ = EStateM.Result.ok () (Storage.withCurrent #[] frame machine) at call
  have runtime := untick s.options s.remaining s.span s.before machine
    (GeneralBorrowPositiveConcreteWindowFunctionRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed)
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have fsize := PositiveRootInstalledFrame.size raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  let tree := GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra tree}
  let slot : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.slotEntry with allocation:=updated}
  let d := s.data
  have tags : GeneralBorrowGcAllocator.NodeTags d.input.tree := by rw [d.treeEq];exact d.nodeTags
  have prepared := GeneralBorrowExposedScopedInactiveWritableProtectedToShared.prepare_mode d.input s.tracker.global.protectedTags s.selected s.head s.extraRoots d.resources tags
    (by rw [d.offsetEq,d.lenEq];exact GeneralBorrowPositiveConcreteWindowInputGeometry.positiveEnd s.toBase)
    (next s.tracker s.fresh).global.nextPointerTag tracker.global.nextPointerTag
    (by rw [d.treeEq];exact s.slotTagFresh) (by rw [d.treeEq];exact s.sharedTagFresh)
    (by rw [d.newTagEq];exact s.slotTagDifferent) (by rw [d.newTagEq];exact s.sharedTagDifferent)
    (by rw [d.treeEq];have bound:=s.nodeRoom;omega)
  dsimp only at prepared
  simp only [d.treeEq,d.parentTagEq,d.newTagEq,d.offsetEq,d.lenEq] at prepared
  obtain ⟨readDone,childDone,borrow,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,protectedEq,resources,supportEq⟩ := prepared
  have treeEq' : borrow.tree=tree := by
    simpa only [tree,GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal] using treeEq
  have tableEq : ((s.tracker.global.protectedTags.insert d.input.newTag .StrongProtector).insert tag .StrongProtector)=tracker.global.protectedTags := by
    rw [d.newTagEq]
    rfl
  have resources' : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor borrow tracker.global.protectedTags s.selected s.head s.extraRoots (fun _=>true) profileMode := by
    exact tableEq ▸ resources
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedData.build borrow tracker.global.protectedTags s.selected s.head s.extraRoots (fun _=>true) resources'
  have sourcePlan := GeneralBorrowExposedScopedInactiveWritableAsMutRawReleaseData.build s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    s.selected s.head s.extraRoots s.data
    (by rw [s.data.offsetEq,s.data.lenEq];exact GeneralBorrowPositiveConcreteWindowInputGeometry.positiveEnd s.toBase)
    (by
      have vacant : s.data.input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index s.data.input)=none := by
        unfold UniValMap.get
        rw [GeneralBorrowFreshMetadataChildMutable.at_end s.data.input]
        simp
      have originalVacant : s.entry.allocation.extra.nodes.get (GeneralBorrowFreshMetadataChildMutable.index s.data.input)=none := by
        exact congrArg (fun t : BorrowTree=>t.nodes.get (GeneralBorrowFreshMetadataChildMutable.index s.data.input)) s.data.treeEq ▸ vacant
      simpa only [s.data.treeEq,GeneralBorrowFreshFutureClean.Clean] using s.vacantClean _ originalVacant)
  have sourceAnchor : sourcePlan.anchor=borrow.parent := by
    apply Option.some.inj
    exact sourcePlan.tagPresent.symm.trans (by
      simpa only [BorrowTree.indexOfTag,treeEq',parentTagEq] using borrow.parentTagPresent)
  have anchorEq : context.anchorNode=sourcePlan.context.anchorNode := by
    apply Option.some.inj
    have left : tree.nodeAt borrow.parent=some context.anchorNode := congrArg (fun t : BorrowTree=>t.nodeAt borrow.parent) treeEq' ▸ context.anchorPresent
    have right : tree.nodeAt borrow.parent=some sourcePlan.context.anchorNode := sourceAnchor ▸ sourcePlan.context.anchorPresent
    exact left.symm.trans right
  have within : GeneralBorrowFreshActiveWithin.ActiveWithin borrow.tree borrow.parent .Write borrow.offset (borrow.offset+borrow.len) := by
    rw [treeEq',parentEq,offsetEq,lenEq]
    exact GeneralBorrowPositiveConcreteWindowFnEntryActivity.source s.toBase s.vacantClean
  have positiveWindow : borrow.offset.toNat<(borrow.offset+borrow.len).toNat := by
    rw [offsetEq,lenEq]
    exact GeneralBorrowPositiveConcreteWindowInputGeometry.positiveEnd s.toBase
  let bufferContext : GeneralBorrowExposedKnownRootRangeData.Context buffer.allocation.extra borrow.parent s.selected s.head s.extraRoots := {
    anchorNode:=context.anchorNode,selectedNode:=context.selectedNode,
    anchorPresent:=by exact congrArg (fun t : BorrowTree=>t.nodeAt borrow.parent) treeEq' ▸ context.anchorPresent,
    selectedPresent:=by exact congrArg (fun t : BorrowTree=>t.nodes.get s.selected) treeEq' ▸ context.selectedPresent,
    roots:=by exact congrArg BorrowTree.roots treeEq' ▸ context.roots,
    depth:=by exact congrArg (fun t : BorrowTree=>t.nodes) treeEq' ▸ context.depth,
    children:=by change GeneralBorrowGraph.ChildNodes tree;exact treeEq' ▸ context.children,
    tags:=by exact congrArg (fun t : BorrowTree=>t.nodes) treeEq' ▸ context.tags }
  let release := GeneralBorrowScopedInactiveWritableWindowDataReturnPlan.build machine.memory tracker.global.protectedTags s.id s.tracker.global.nextPointerTag buffer
    (GenericFunctionEntryState.buffer_lookup rawMachine s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated (Ne.symm s.separate))
    borrow.parent s.selected s.head s.extraRoots bufferContext
    (by change context.anchorNode.isExposed=false;rw [anchorEq];exact sourcePlan.hidden)
    (by change tree.indexOfTag s.tracker.global.nextPointerTag=some borrow.parent;rw [←treeEq',←parentTagEq];exact borrow.parentTagPresent)
    borrow.offset borrow.len positiveWindow
    (by change tree.locations.WellFormed;rw [←treeEq'];exact borrow.well)
    (by change GeneralBorrowFreshActiveWithin.ActiveWithin tree borrow.parent .Write borrow.offset (borrow.offset+borrow.len);rw [←treeEq'];exact within)
    (by change tree.nodes.data.size≤4294967296;rw [←treeEq'];change borrow.tree.nodes.size≤4294967296;have bound:=resources'.room;omega)
    resources'.component.support
    (by simpa only [buffer,Allocation.setExtra,Allocation.mapExtra,treeEq'] using owned)
    s.slotId s.separate slot (MemoryCopyBridge.live_lookup_replaced _ s.slotId slot) s.slotRoot tag slotTree
    (GenericFunctionEntryState.buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct s.slotFree)
    (GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh) s.slotDistinct
  obtain ⟨thread,activeThread,top⟩ := runtime.active
  let input : GeneralBorrowScopedInactiveWritableRootZeroPhysical.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,source:=s.source,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=frame,size:=fsize,location:=floc,slot0:=by simpa using slots ⟨0,by decide⟩,
    slot3:=by simpa using slots ⟨3,by decide⟩,slot4:=by simpa using slots ⟨4,by decide⟩,slot5:=by simpa using slots ⟨5,by decide⟩,
    slot2:=by simpa using slots ⟨2,by decide⟩,
    immediate:=PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals s.before s.place s.race) adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag,
    body:=fb.trans raw.body,identity:=fi.trans raw.identity,callee:=fc.trans raw.callee,noLocalClocks:=frace.trans raw.noClocks,
    continuation:=frc.trans (RawRootInvocation.control s.before s.place s.race).2.2.1,varargs:=by rw [fva];rfl,
    machine:=machine,tracker:=tracker,tracked:=rfl,defaultMode:=s.mode,noClocks:=runtime.race,noBackend:=runtime.backend,
    ghost:=runtime.ghost,shallow:=runtime.shallow,unchecked:=runtime.unchecked,noGc:=runtime.noGc,fixed:=runtime.fixed,
    thread:=thread,active:=activeThread,release:=release,frameTracked:=by
      change frame.extra.borrowTracker=some (GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.frame release)
      simpa only [release,GeneralBorrowScopedInactiveWritableWindowDataReturnPlan.build,GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.frame,parentTagEq] using fborrow,
    slotSize:=slotSize,slotStorage:=slotLen,slotMask:=slotMask,slotProvenance:=slotProv,slotMutable:=slotMut,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [runtime.addresses];exact s.slotCached,
    extras:=by change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [runtime.extras];exact s.extras,
    destination:=by rw [frp];rfl }
  exact ⟨input,rfl,rfl,rfl,rfl,call⟩

theorem invoke {profileMode : ProfileMode} (s : InitialFor profileMode) :
    ∃ input : GeneralBorrowScopedInactiveWritableRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) ∧ GeneralBorrowScopedInactiveWritableRootZeroPhysical.Result input := by
  obtain ⟨input,options,limits,remaining,span,call⟩ := prepare s
  exact ⟨input,options,limits,remaining,span,call,GeneralBorrowScopedInactiveWritableRootZeroPhysical.complete input⟩

end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowZero
