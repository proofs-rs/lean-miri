import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionSharedCallPrefixMetadata
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionOriginalInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionSharedCallPrefixBase
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-- Initial raw caller data derives the actual shared-expression prefix. -/
theorem enters_pre_len_base (s : GeneralBorrowPositiveWildcardPartitionOriginalInput.Base)
    (countPositive : (0 : UInt64)<s.count) :
    let cfg := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let sharedValue := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id (GeneralBorrowPositiveWildcardPartitionFunctionState.held s.tracker s.fresh s.slotFresh).global.nextPointerTag) (Size.ofBytes s.base)) s.len SharedReferenceMetadata.sharedLayout).imm
    ∃ installed beforeShared sharedFrame sharedMachine slotAllocation, ∃ input : GeneralBorrowFreshMetadataChildShared.Input,
      let held := GeneralBorrowPositiveWildcardPartitionFunctionState.held s.tracker s.fresh s.slotFresh
      let current := RootZeroCompleteState.tick s.options s.remaining s.span
        (GeneralBorrowPositiveWildcardPartitionFunctionState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation)
      let buffer := {s.entry with allocation := s.entry.allocation.setExtra (GeneralBorrowPositiveWildcardPartitionArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.len)}
      let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm
      let entryFrame := PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) adjusted s.count {} s.id s.tracker.global.nextPointerTag
        s.slotId (GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed (Storage.withCurrent #[] sharedFrame sharedMachine) ∧
      GeneralBorrowForestSharedPreLenFrame.Facts beforeShared sharedFrame s.count sharedValue ∧
      GenericFunctionEntryPrefix.Shape entryFrame beforeShared s.count ∧
      GeneralBorrowPositiveWildcardPartitionFunctionToShared.Ready beforeShared adjusted s.count
        ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
          (GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag) ∧
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
      slotAllocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (GeneralBorrowPositiveWildcardPartitionFunctionState.next s.tracker s.fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧ slotAllocation.provenanceMap = ProvenanceMap.new ∧
      AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot s.slotEntry.allocation ∧ slotAllocation.mutability = .Mut := by
  exact GeneralBorrowPositiveWildcardPartitionSharedCallPrefixMetadata.enters_pre_len
    (options := s.options) (limits := s.limits) (remaining := s.remaining) (span := s.span) (ctx := s.ctx)
    (debugOff := s.debugOff) (cmp := s.cmp) (dynamicFuel := s.dynamicFuel) (validityFuel := s.validityFuel) (fuelEq := s.fuelEq)
    (validationEq := s.validationEq) (id := s.id) (tracker := s.tracker) (base := s.base) (len := s.len)
    (count := s.count) (nonzero := s.nonzero) (entry := s.entry) (positive := s.positive) (signedFits := s.signedFits)
    (bounds := s.bounds) (before := s.before) (ghost := s.ghost) (shallow := s.shallow) (cachedAddress := s.cachedAddress)
    (present := s.present) (enabled := s.enabled) (fresh := s.fresh) (position := s.position) (positionValid := s.positionValid)
    (ordered := s.ordered) (addressRow := s.addressRow) (addressMode := s.addressMode) (exposedAlloc := s.exposedAlloc) (head := s.head)
    (headNode := s.headNode) (extraRoots := s.extraRoots) (nodes := s.nodes) (roots := s.roots) (headPresent := s.headPresent)
    (headLeaf := s.headLeaf) (headExposed := s.headExposed) (short := s.short) (other := s.other) (well := s.initialState.well)
    (treeBounds := (by simp only [s.full,Nat.le_refl])) (sourceAt := (GeneralBorrowPositiveWildcardPartitionOriginalInput.source_at s)) (tagFresh := s.tagFresh) (noFree := s.noFree) (fits := s.fits)
    (race := s.race) (metadata := s.metadata) (notConstructed := s.notConstructed) (retagCtx := s.retagCtx) (place := s.place)
    (layout := s.layout) (slotId := s.slotId) (slotEntry := s.slotEntry) (slotBase := s.slotBase) (slotRoot := s.slotRoot)
    (slotPointer := s.slotPointer) (aligned := s.aligned) (slotCached := s.slotCached) (slotTree := s.slotTree) (slotSize := s.slotSize)
    (slotPresent := s.slotPresent) (separate := s.separate) (slotFresh := s.slotFresh) (slotDistinct := s.slotDistinct) (slotParentDistinct := s.slotParentDistinct)
    (slotFree := s.slotFree) (mutable := s.mutable) (storage := s.storage) (maskLength := s.maskLength) (provenance := s.provenance)
    (noBackend := s.noBackend) (extras := s.extras) (thread := s.thread) (active := s.active) (noCache := s.noCache)
    (source := s.source) (mode := s.mode) (countPositive := countPositive) (unchecked := s.unchecked) (noGc := s.noGc)
    (fixed := s.fixed) (initialState := s.initialState) (bufferSize := s.bufferSize) (mapAligned := s.mapAligned) (nodeRoom := s.nodeRoom)
    (scope := s.scope) (allLeaves := s.allLeaves) (full := s.full) (unique := s.unique) (coherent := s.coherent)
    (slotTagFresh := s.slotTagFresh) (sharedTagFresh := s.sharedTagFresh) (slotTagDifferent := s.slotTagDifferent) (sharedTagDifferent := s.sharedTagDifferent) (sharedFresh := s.sharedFresh)
    (preciseOff := s.preciseOff) (implicitOff := s.implicitOff)
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionSharedCallPrefixBase
