import duplicate_prefix.GeneralBorrowPositiveConcreteWindowInputGeometry
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFinalState
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableFunctionEntryToShared
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedToShared
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowSharedStatement
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowSharedCallPrefixMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open Miri.DataStructures GeneralBorrowPositiveConcreteWindowInputGeometry
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private def moveResources {profileMode : ProfileMode} {input : GeneralBorrowFreshMetadataChildShared.Input} {before after : ProtectedTags}
    {selected head : UniIndex} {tail : List UniIndex} (same : before=after)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input before selected head tail (fun _=>true) profileMode) :
    GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input after selected head tail (fun _=>true) profileMode := same ▸ raw
private theorem move_support {profileMode : ProfileMode} {input : GeneralBorrowFreshMetadataChildShared.Input} {before after : ProtectedTags}
    {selected head : UniIndex} {tail : List UniIndex} (same : before=after)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input before selected head tail (fun _=>true) profileMode) :
    (moveResources same raw).component.support=raw.component.support := by
  cases same
  rfl

/-- The genuine original concrete caller reaches the real shared-expression
boundary from initial selected-component data, retaining allocation-relative
window addresses and all actual frame/slot metadata. -/
theorem enters_pre_len {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (countPositive : (0 : UInt64)<s.count) :
    let cfg := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let sharedValue := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id (GenericFunctionEntryState.held s.tracker s.fresh s.slotFresh).global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len SharedReferenceMetadata.sharedLayout).imm
    ∃ installed beforeShared sharedFrame sharedMachine slotAllocation, ∃ input : GeneralBorrowFreshMetadataChildShared.Input,
      let held := GenericFunctionEntryState.held s.tracker s.fresh s.slotFresh
      let current := RootZeroCompleteState.tick s.options s.remaining s.span
        (GenericFunctionEntryState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation)
      let buffer := {s.entry with allocation := s.entry.allocation.setExtra (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)}
      let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
      let entryFrame := PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag
        s.slotId (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed (Storage.withCurrent #[] sharedFrame sharedMachine) ∧
      GeneralBorrowForestSharedPreLenFrame.Facts beforeShared sharedFrame s.count sharedValue ∧
      GenericFunctionEntryPrefix.Shape entryFrame beforeShared s.count ∧
      GeneralBorrowExposedScopedInactiveWritableFunctionEntryToShared.Ready beforeShared adjusted s.count
        ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
          (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag) ∧
      (∃ valid : 12 < beforeShared.locals.size, sharedFrame = GeneralBorrowForestSharedPreLenFrame.after beforeShared valid sharedValue) ∧
      input.tree = buffer.allocation.extra ∧ input.parentTag = s.tracker.global.nextPointerTag ∧
      input.newTag = held.global.nextPointerTag ∧ input.parent = GeneralBorrowFreshMetadataChildMutable.index s.data.input ∧
      input.isProtected = false ∧ input.offset = s.offset ∧ input.len = s.len ∧
      (∃ raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input held.global.protectedTags
        s.selected s.head s.extraRoots (fun _=>true) profileMode,
        raw.component.support = (fun componentPosition => s.data.resources.component.support componentPosition ∨ componentPosition = (GeneralBorrowFreshMetadataChildMutable.index s.data.input).toNat)) ∧
      sharedMachine = {ReferenceBorrowDriver.allocatedMachine current held s.sharedFresh with
        memory := RetagEntry.updatedMemory current.memory s.id buffer (GeneralBorrowForestMixedShared.child buffer.allocation.extra held.global.protectedTags
          s.tracker.global.nextPointerTag held.global.nextPointerTag false s.offset s.len .VisitChildrenOfAccessed).tree} ∧
      slotAllocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧ slotAllocation.provenanceMap = ProvenanceMap.new ∧
      AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot s.slotEntry.allocation ∧ slotAllocation.mutability = .Mut := by
  dsimp only
  have allocationSize : s.entry.allocation.extra.locations.size=s.entry.allocation.byteSize := by
    rw [s.bufferSize]
    exact congrArg Size.ofBytes s.allocationCapacity
  obtain ⟨slotAllocation,result,call,trace,shape,ready,slotProps⟩ :=
    GeneralBorrowExposedScopedInactiveWritableFunctionEntryToShared.enters_shared_boundary s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq
      s.id s.parentTag s.tracker s.base s.offset s.len s.count (nonzero s) s.entry s.positive s.signedFits (byteBounds s) s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh
      s.selected s.head s.extraRoots s.data allocationSize s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize
      s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache
      s.source s.mode countPositive s.unchecked s.noGc s.fixed
  let held := GenericFunctionEntryState.held s.tracker s.fresh s.slotFresh
  let initialMachine := GenericFunctionEntryState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation
  let current := RootZeroCompleteState.tick s.options s.remaining s.span initialMachine
  let buffer := {s.entry with allocation := s.entry.allocation.setExtra (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)}
  let d := s.data
  have tags : GeneralBorrowGcAllocator.NodeTags d.input.tree := by rw [d.treeEq];exact d.nodeTags
  have prepared :=
    GeneralBorrowExposedScopedInactiveWritableProtectedToShared.prepare_mode d.input s.tracker.global.protectedTags s.selected s.head s.extraRoots d.resources tags
      (by rw [d.offsetEq,d.lenEq];exact positiveEnd s) (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag held.global.nextPointerTag
      (by rw [d.treeEq];exact s.slotTagFresh) (by rw [d.treeEq];exact s.sharedTagFresh)
      (by rw [d.newTagEq];exact s.slotTagDifferent) (by rw [d.newTagEq];exact s.sharedTagDifferent)
      (by rw [d.treeEq];have bound:=s.nodeRoom;omega)
  dsimp only at prepared
  simp only [d.treeEq,d.parentTagEq,d.newTagEq,d.offsetEq,d.lenEq] at prepared
  obtain ⟨readDone,childDone,input,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,protectedEq,raw,supportEq⟩ := prepared
  have treeEq' : input.tree=buffer.allocation.extra := by
    simpa only [buffer,GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,Allocation.setExtra,Allocation.mapExtra] using treeEq
  have parentTagEq' : input.parentTag=s.tracker.global.nextPointerTag := parentTagEq
  have offsetEq' : input.offset=s.offset := offsetEq
  have lenEq' : input.len=s.len := lenEq
  have tableEq : ((s.tracker.global.protectedTags.insert d.input.newTag .StrongProtector).insert
      (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag .StrongProtector)=held.global.protectedTags := by
    rw [d.newTagEq]
    rfl
  let raw' := moveResources tableEq raw
  have supportEq' : raw'.component.support=(fun position=>d.resources.component.support position∨position=(GeneralBorrowFreshMetadataChildMutable.index d.input).toNat) :=
    (move_support tableEq raw).trans supportEq
  have bufferPresent : current.memory.live.find? (fun row => row.1 == s.id) = some (s.id,buffer) := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact GenericFunctionEntryState.buffer_lookup (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation (Ne.symm s.separate)
  have currentEnabled : current.borrowTracker = some held := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    rfl
  have currentGhost : current.user.payload.ghost = false := by
    rw [show current.user.payload.ghost = initialMachine.user.payload.ghost from RootZeroCompleteState.tick_ghost s.options s.remaining s.span initialMachine]
    exact s.ghost
  have currentShallow : current.user.payload.validation = .Shallow := by
    rw [show current.user.payload.validation = initialMachine.user.payload.validation from RootZeroCompleteState.tick_shallow s.options s.remaining s.span initialMachine]
    exact s.shallow
  have currentAddress : current.user.addresses.baseAddr.find? (fun row => row.allocId == s.id) = some ⟨s.id,s.base⟩ := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact s.cachedAddress
  have currentRace : current.dataRace = none := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact s.race
  have currentMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result current)).metadata = PreparedReflection.actual.runtime := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact s.metadata
  have currentNotConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result current)).entries.any (·.value.ty == 4) = false := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact s.notConstructed
  have capacity : buffer.allocation.extra.locations.size=buffer.allocation.byteSize := by
    change (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len).locations.size=s.entry.allocation.byteSize
    rw [(GeneralBorrowPositiveConcreteWindowFinalState.build s).2.1]
    exact allocationSize
  have ready' : GeneralBorrowExposedScopedInactiveWritableFunctionEntryToShared.Ready result
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).access.runtime.base
        (Pointer.new (.concrete s.id input.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm s.count
        ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (GenericFunctionEntryState.next s.tracker s.fresh).global.nextPointerTag) := by
    simpa only [parentTagEq',ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime] using ready
  obtain ⟨valid,step,facts⟩ := GeneralBorrowPositiveConcreteWindowSharedStatement.executes_from_ready s.options s.limits s.remaining s.span s.preciseOff s.implicitOff s.debugOff s.cmp
    s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.base s.offset s.len s.id buffer s.positive (nonzero s) s.signedFits #[] result current
    held currentEnabled s.mode s.sharedFresh input s.selected s.head s.extraRoots (fun _=>true) raw' treeEq' newTagEq offsetEq' lenEq' capacity s.count _ ready'
    currentGhost currentShallow currentAddress bufferPresent currentRace currentMetadata currentNotConstructed
  refine ⟨_,result,_,_,slotAllocation,input,call,SuccessfulTrace.append trace (.next step (.refl _)),?_,shape,ready,⟨valid,?_⟩,treeEq',parentTagEq',newTagEq,parentEq,protectedEq,offsetEq',lenEq',⟨raw',?_⟩,?_,slotProps⟩
  · simpa only [RootReferenceInfo.layout,ite_true,held] using facts
  · simp only [RootReferenceInfo.layout,ite_true,held]
  · exact supportEq'
  · simp only [parentTagEq']
    rfl
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowSharedCallPrefixMetadata
