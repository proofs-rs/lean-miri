import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableFunctionEntryInvocation
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowInvocationBase
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open RootFrameData EmptyRootArguments PositiveRootArguments GeneralBorrowExposedScopedInactiveWritableFunctionEntryScope
open Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-- Raw allocation-relative window data derive the actual physical entry. -/
theorem enters {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (count : UInt64) :
    let value := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
    let argsFrame := RootArgumentsTwo.result (PositiveRootArguments.firstDone (RawRootInvocation.root s.before s.place s.race) adjusted ({} : FrameState) s.id s.tracker.global.nextPointerTag) count
    let argsMachine := resultMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal s.tracker.global s.fresh,s.tracker.retagMode⟩
    let owned := ({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState #[] changed owned argsMachine next s.slotFresh s.slotId s.slotEntry
      (PhysicalMachineWrite.slotTree s.slotRoot next.global.nextPointerTag 1 false)
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
      .ok () (Storage.withCurrent #[]
        (CallEntryFacts.doneRootFrame {registeredFrame changed owned s.slotId next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed s.slotId s.slotEntry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree s.slotRoot next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot s.slotEntry.allocation ∧
      updated.mutability = .Mut := by
  let layout : GeneralBorrowPositiveWildcardWindowLayout.Layout := ⟨s.base,s.capacity,s.offset,s.len,s.nonzero,s.positive,s.bounds,s.addressFits⟩
  have pointerFits : s.base.toNat+s.offset.toNat+s.len.toNat<2^64 := by
    have bounded:=s.bounds
    have fits:=s.addressFits
    omega
  exact GeneralBorrowExposedScopedInactiveWritableFunctionEntryInvocation.enters
    (options := s.options) (limits := s.limits) (remaining := s.remaining) (span := s.span) (ctx := s.ctx)
    (debugOff := s.debugOff) (cmp := s.cmp) (dynamicFuel := s.dynamicFuel) (validityFuel := s.validityFuel) (fuelEq := s.fuelEq)
    (validationEq := s.validationEq) (id := s.id) (tracker := s.tracker) (base := s.base) (offset := s.offset)
    (len := s.len) (n := count) (nonzero := (GeneralBorrowPositiveWildcardWindowLayout.address_nonzero layout)) (entry := s.entry) (positive := s.positive)
    (signedFits := s.signedFits) (bounds := (by rw [s.bufferSize];exact s.bounds)) (before := s.before) (ghost := s.ghost)
    (shallow := s.shallow) (cachedAddress := s.cachedAddress) (present := s.present) (enabled := s.enabled) (fresh := s.fresh)
    (selected := s.selected) (head := s.head) (tail := s.extraRoots) (data := s.data)
    (capacity := (by rw [s.bufferSize];exact congrArg Size.ofBytes s.allocationCapacity))
    (race := s.race) (metadata := s.metadata) (notConstructed := s.notConstructed) (retagCtx := s.retagCtx)
    (place := s.place) (layout := s.layout) (slotId := s.slotId) (slotEntry := s.slotEntry) (slotBase := s.slotBase)
    (slotRoot := s.slotRoot) (slotPointer := s.slotPointer) (aligned := s.aligned) (slotCached := s.slotCached) (slotTree := s.slotTree)
    (slotSize := s.slotSize) (slotPresent := s.slotPresent) (separate := s.separate) (slotFresh := s.slotFresh) (slotDistinct := s.slotDistinct)
    (slotParentDistinct := s.slotParentDistinct) (slotFree := s.slotFree) (mutable := s.mutable) (storage := s.storage) (maskLength := s.maskLength)
    (provenance := s.provenance) (noBackend := s.noBackend) (extras := s.extras) (thread := s.thread) (active := s.active)
    (noCache := s.noCache)
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowInvocationBase
