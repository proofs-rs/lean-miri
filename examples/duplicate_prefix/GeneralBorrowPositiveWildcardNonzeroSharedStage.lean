import duplicate_prefix.GeneralBorrowPositiveWildcardNonzeroInput
import duplicate_prefix.GeneralBorrowPositiveWildcardSharedCallPrefixMetadata
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardNonzeroSharedStage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The common original caller contract forms the real positive shared
expression prefix, retaining its exact physical frame and raw source resources. -/
theorem enters (s : GeneralBorrowPositiveWildcardNonzeroInput.Initial) :
    let cfg := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let sharedValue := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id (GeneralBorrowPositiveWildcardFunctionState.held s.tracker s.fresh s.slotFresh).global.nextPointerTag) (Size.ofBytes s.base)) s.len SharedReferenceMetadata.sharedLayout).imm
    ∃ installed beforeShared sharedFrame sharedMachine slotAllocation, ∃ input : GeneralBorrowFreshMetadataChildShared.Input,
      let held := GeneralBorrowPositiveWildcardFunctionState.held s.tracker s.fresh s.slotFresh
      let current := RootZeroCompleteState.tick s.options s.remaining s.span
        (GeneralBorrowPositiveWildcardFunctionState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation)
      let buffer := {s.entry with allocation := s.entry.allocation.setExtra (GeneralBorrowPositiveWildcardArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.len)}
      let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm
      let entryFrame := PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag
        s.slotId (GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed (Storage.withCurrent #[] sharedFrame sharedMachine) ∧
      GeneralBorrowForestSharedPreLenFrame.Facts beforeShared sharedFrame s.count sharedValue ∧
      GenericFunctionEntryPrefix.Shape entryFrame beforeShared s.count ∧
      GeneralBorrowPositiveWildcardFunctionToShared.Ready beforeShared adjusted s.count
        ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
          (GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag) ∧
      (∃ valid : 12 < beforeShared.locals.size, sharedFrame = GeneralBorrowForestSharedPreLenFrame.after beforeShared valid sharedValue) ∧
      input.tree = buffer.allocation.extra ∧ input.parentTag = s.tracker.global.nextPointerTag ∧
      input.newTag = held.global.nextPointerTag ∧ input.parent = ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ ∧
      input.isProtected = false ∧ input.offset = 0 ∧ input.len = s.len ∧
      (∃ raw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources input held.global.protectedTags
        ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ s.head
        (s.extraRoots++[⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩]) (fun _=>true),
        raw.component.support = (fun position => position = (⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ : UniIndex).toNat)) ∧
      sharedMachine = {ReferenceBorrowDriver.allocatedMachine current held s.sharedFresh with
        memory := RetagEntry.updatedMemory current.memory s.id buffer (GeneralBorrowForestMixedShared.child buffer.allocation.extra held.global.protectedTags
          s.tracker.global.nextPointerTag held.global.nextPointerTag false 0 s.len .VisitChildrenOfAccessed).tree} ∧
      slotAllocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧ slotAllocation.provenanceMap = ProvenanceMap.new ∧
      AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot s.slotEntry.allocation ∧ slotAllocation.mutability = .Mut := by
  exact GeneralBorrowPositiveWildcardSharedCallPrefixMetadata.enters_pre_len
    s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.tracker s.base s.len s.count s.nonzero s.entry s.positive s.signedFits s.bounds s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh s.position s.positionValid s.ordered s.addressRow s.addressMode s.exposedAlloc s.location s.head s.headNode s.extraRoots s.nodes s.states s.locations s.roots s.headPresent s.headLeaf s.headExposed s.headStored s.coherent s.short s.data s.tagFresh s.noFree s.fits s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache s.source s.mode s.countPositive s.unchecked s.noGc s.fixed s.initialState s.bufferSize s.mapAligned s.nodeRoom s.scope s.allLeaves s.slotTagFresh s.sharedTagFresh s.slotTagDifferent s.sharedTagDifferent s.sharedFresh s.preciseOff s.implicitOff
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardNonzeroSharedStage
