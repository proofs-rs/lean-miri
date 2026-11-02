import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionPreparedRegistration
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionInvocationBase
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionOriginalInput
import duplicate_prefix.GenericFunctionEntryNumerics
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionRuntime
import duplicate_prefix.GeneralBorrowPositiveWildcardReleaseActivity
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionZero
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowPositiveWildcardPartitionFunctionState
open Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Initial extends GeneralBorrowPositiveWildcardPartitionOriginalInput.Base where
  zero : count=0

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
theorem prepare (s : Initial) :
    ∃ input : GeneralBorrowScopedRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowPositiveWildcardPartitionInvocationBase.enters s.toBase 0
  let raw := RawRootInvocation.root s.before s.place s.race
  let rawMachine := RawRootInvocation.machine #[] s.before
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm
  let tag := (next s.tracker s.fresh).global.nextPointerTag
  let tracker := held s.tracker s.fresh s.slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  let machine := enteredMachine rawMachine s.tracker s.fresh s.id s.entry s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
  rw [GeneralBorrowPositiveWildcardPartitionFunctionState.entered_eq] at call
  have runtime := untick s.options s.remaining s.span s.before machine
    (GeneralBorrowPositiveWildcardPartitionRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed)
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have fsize := PositiveRootInstalledFrame.size raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  let tree := GeneralBorrowPositiveWildcardPartitionArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.len
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra tree}
  let slot : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.slotEntry with allocation:=updated}
  obtain ⟨borrow,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,resources,supportEq⟩ :=
    GeneralBorrowPositiveWildcardPartitionPreparedRegistration.build_registered s.entry.allocation.extra s.initialState s.len
      (UInt64.pos_iff_ne_zero.mp s.positive) s.full s.head s.extraRoots s.roots s.scope s.tracker.global.nextPointerTag tracker.global.nextPointerTag
      s.tagFresh s.sharedTagFresh s.sharedTagDifferent s.noFree s.mapAligned s.nodeRoom
      tag s.slotTagFresh s.slotTagDifferent (TypedBorrowSteps.registeredGlobal s.tracker s.tracker.global.nextPointerTag).protectedTags s.coherent s.allLeaves s.unique
  let resources' : GeneralBorrowExposedScopedSharedLeafConstructor.Resources borrow tracker.global.protectedTags
    ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.head
    (s.extraRoots++[⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩]) (fun _=>true) := resources
  have treeEq' : borrow.tree=tree := treeEq
  let prepared := GeneralBorrowRangePrepareState.prepared s.entry.allocation.extra Size.ZERO (Size.ofBytes s.len)
  have bounds : (0 : UInt64).toNat+s.len.toNat≤s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.full];simp
  have preparedState := GeneralBorrowRangePrepareState.state s.entry.allocation.extra Size.ZERO (Size.ofBytes s.len) s.initialState bounds
  have cap : prepared.locations.size.bytes=s.len := (congrArg Size.bytes preparedState.2).trans s.full
  have activity := GeneralBorrowPositiveWildcardReleaseActivity.source prepared
    ⟨s.entry.allocation.extra.tagMapping.mapping.push (s.tracker.global.nextPointerTag,⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩),s.entry.allocation.extra.tagMapping.deassigned⟩
    ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.tracker.global.nextPointerTag s.len s.positive preparedState.1.well cap
  have active : GeneralBorrowFreshReleaseLoop.ActiveOn borrow.tree borrow.parent .Read borrow.offset (borrow.offset+borrow.len) := by
    rw [treeEq',parentEq,offsetEq,lenEq,UInt64.zero_add]
    exact activity.1
  have matching : ∀ position (valid : position<borrow.tree.locations.entries.size) state,
      borrow.tree.locations.entries[position].data.perms.get borrow.parent=some state → state.accessed=true →
      ∀ kind,state.permission.associatedAccess=some kind → kind=.Read := by
    rw [treeEq',parentEq]
    exact activity.2
  have rangePositive : borrow.offset.toNat<(borrow.offset+borrow.len).toNat := by
    rw [offsetEq,lenEq,UInt64.zero_add]
    exact UInt64.lt_iff_toNat_lt.mp s.positive
  let release := GeneralBorrowScopedResourcesReturnPlan.build machine.memory tracker.global.protectedTags borrow
    ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.head (s.extraRoots++[⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩])
    .Read resources' rangePositive active matching s.id buffer
    (GeneralBorrowPositiveWildcardPartitionFunctionState.buffer_lookup rawMachine s.tracker s.fresh s.id s.entry s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated (Ne.symm s.separate)) treeEq'.symm
    s.slotId s.separate slot (MemoryCopyBridge.live_lookup_replaced _ s.slotId slot) s.slotRoot tag slotTree
    (GenericFunctionEntryState.buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct s.slotFree)
    (GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh) s.slotDistinct
  obtain ⟨thread,activeThread,top⟩ := runtime.active
  let input : GeneralBorrowScopedRootZeroPhysical.Input := {
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
      change frame.extra.borrowTracker=some (GeneralBorrowScopedPhysicalReturnPlan.frame release)
      simpa only [release,GeneralBorrowScopedResourcesReturnPlan.build,GeneralBorrowScopedPhysicalReturnPlan.frame,parentTagEq] using fborrow,
    slotSize:=slotSize,slotStorage:=slotLen,slotMask:=slotMask,slotProvenance:=slotProv,slotMutable:=slotMut,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [runtime.addresses];exact s.slotCached,
    extras:=by change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [runtime.extras];exact s.extras,
    destination:=by rw [frp];rfl }
  exact ⟨input,rfl,rfl,rfl,rfl,call⟩

theorem invoke (s : Initial) :
    ∃ input : GeneralBorrowScopedRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) ∧ GeneralBorrowScopedRootZeroPhysical.Result input := by
  obtain ⟨input,options,limits,remaining,span,call⟩ := prepare s
  exact ⟨input,options,limits,remaining,span,call,GeneralBorrowScopedRootZeroPhysical.complete input⟩

end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionZero
