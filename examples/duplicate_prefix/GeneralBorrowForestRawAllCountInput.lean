import duplicate_prefix.GeneralBorrowForestAllCountSafety
import duplicate_prefix.GeneralBorrowForestTagHighWater
namespace DuplicatePrefix.GeneralBorrowForestRawAllCountInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open ActualReferenceContext GenericFunctionEntryState GenericFunctionTagFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

set_option autoImplicit false in
/-- Original physical/base-zero contract plus one raw tag high-water reserve.
All generated expression/helper/default/FnEntry tag facts and computed helper
protector flags are derived by `toInitial`, rather than supplied by the caller. -/
structure Initial extends toOriginal : GeneralBorrowForestFunctionEntryZero.Initial where
  count : UInt64
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  statementFuel : limits.validation = validityFuel+1
  allocator : GeneralBorrowGcAllocator.Invariant entry.allocation.extra
  room : entry.allocation.extra.nodes.size+8 ≤ 4294967295
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  storageBuffer : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValidBuffer : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLengthBuffer : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initializedBuffer : count ≤ len/2 → InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenanceBuffer : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFitsBuffer : entry.allocation.len+64 < 18446744073709551616
  mutableBuffer : entry.allocation.mutability = .Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ len/2 → count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes

  highWater : GeneralBorrowForestTagHighWater.Below entry.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag
  slotBelow : slotRoot.value.toNat < tracker.global.nextPointerTag.value.toNat
  tagRoom : tracker.global.nextPointerTag.value.toNat+6 ≤ 18446744073709551615

def chain (s : Initial) : Chain s.tracker := from_room s.tracker s.tagRoom

def below (s : Initial) : GenericFunctionTagFormation.Below s.entry.allocation.extra s.tracker.global.protectedTags s.tracker.global.nextPointerTag :=
  GeneralBorrowForestTagHighWater.complete _ _ _ s.highWater s.allocator.nodeTags

theorem formed (s : Initial) :
    (∀ index : Fin 4, GeneralBorrowTagMap.Fresh s.entry.allocation.extra.tagMapping (future s.tracker (chain s) index) ∧
      GeneralBorrowProtector.Fresh s.entry.allocation.extra (future s.tracker (chain s) index) ∧
      s.tracker.global.protectedTags.contains (future s.tracker (chain s) index)=false ∧
      (expr s.tracker (chain s)).global.protectedTags.contains (future s.tracker (chain s) index)=false) ∧
    Function.Injective (future s.tracker (chain s)) := GenericFunctionTagFormation.formed s.entry.allocation.extra s.tracker (chain s) (below s)

theorem root_different (s : Initial) (index : Fin 4) : s.tracker.global.nextPointerTag ≠ future s.tracker (chain s) index := by
  apply GeneralBorrowForestTagHighWater.different
  have value := future_value s.tracker (chain s) index
  omega

theorem slot_different (s : Initial) (index : Fin 4) : (next s.tracker s.fresh).global.nextPointerTag ≠ future s.tracker (chain s) index := by
  apply GeneralBorrowForestTagHighWater.different
  have value := future_value s.tracker (chain s) index
  have slot := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  change (next s.tracker s.fresh).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+1 at slot
  omega

theorem future_different (s : Initial) (left right : Fin 4) (different : left≠right) :
    future s.tracker (chain s) left ≠ future s.tracker (chain s) right := fun same => different ((formed s).2 same)

def afterHelper (s : Initial) : GlobalState :=
  (TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) (chain s).exprFresh) (chain s).helperFresh)
    (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) (chain s).exprFresh).global.nextPointerTag).global.endCall
    (({} : FrameState).addProtector s.id (ReferenceBorrowDriver.allocatedTracker (held s.tracker s.fresh s.slotFresh) (chain s).exprFresh).global.nextPointerTag)

theorem helper_table (s : Initial) : (afterHelper s).protectedTags =
    (((held s.tracker s.fresh s.slotFresh).global.protectedTags.insert (future s.tracker (chain s) ⟨1,by decide⟩) .StrongProtector).remove
      (future s.tracker (chain s) ⟨1,by decide⟩)) := by
  simp only [afterHelper,GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rfl

theorem helper_flags (s : Initial) : (afterHelper s).protectedTags.contains s.slotRoot=false ∧
    (afterHelper s).protectedTags.contains (next s.tracker s.fresh).global.nextPointerTag=true := by
  have rootDifferent : s.slotRoot≠s.tracker.global.nextPointerTag := GeneralBorrowForestTagHighWater.different _ _ s.slotBelow
  have slotValue := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  change (next s.tracker s.fresh).global.nextPointerTag.value.toNat=s.tracker.global.nextPointerTag.value.toNat+1 at slotValue
  have slotDifferent : s.slotRoot≠(next s.tracker s.fresh).global.nextPointerTag := by
    apply GeneralBorrowForestTagHighWater.different
    have low := s.slotBelow
    omega
  have free := buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot rootDifferent slotDifferent s.slotFree
  have held := GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh
  rw [helper_table]
  exact GeneralBorrowForestTagHighWater.helper_flags _ _ _ _ s.id
    (Ne.symm (slot_root_future s.tracker (chain s) s.slotRoot s.slotBelow ⟨1,by decide⟩)) (slot_different s ⟨1,by decide⟩) free held


/-- Form the frozen all-count physical input from original high-water data.
Every future-tag freshness/overflow/distinctness and computed helper flag is
proved above; no after-helper condition or operation success is an input. -/
def toInitial (s : Initial) : GeneralBorrowForestAllCountInput.Initial := {
  toOriginal := s.toOriginal
  count := s.count
  preciseOff := s.preciseOff
  implicitOff := s.implicitOff
  budget := s.budget
  dispatchFuel := s.dispatchFuel
  statementFuel := s.statementFuel
  allocator := s.allocator
  room := s.room
  vacantClean := s.vacantClean
  storageBuffer := s.storageBuffer
  maskValidBuffer := s.maskValidBuffer
  maskLengthBuffer := s.maskLengthBuffer
  initializedBuffer := s.initializedBuffer
  provenanceBuffer := s.provenanceBuffer
  storageFitsBuffer := s.storageFitsBuffer
  mutableBuffer := s.mutableBuffer
  bufferExtras := s.bufferExtras
  bounded := s.bounded
  fresh3 := (chain s).exprFresh
  fresh4 := (chain s).helperFresh
  fresh5 := (chain s).mutFresh
  fresh6 := (chain s).mutEntryFresh
  exprUnheld := ((formed s).1 ⟨0,by decide⟩).2.2.2
  helperUnheld := GeneralBorrowForestTagHighWater.get_none _ _ (((formed s).1 ⟨1,by decide⟩).2.2.2)
  rootFreeAfterHelper := (helper_flags s).1
  slotHeldAfterHelper := (helper_flags s).2
  exprFresh := ((formed s).1 ⟨0,by decide⟩).1
  helperFresh := ((formed s).1 ⟨1,by decide⟩).1
  rootExprDifferent := root_different s ⟨0,by decide⟩
  rootHelperDifferent := root_different s ⟨1,by decide⟩
  map5 := ((formed s).1 ⟨2,by decide⟩).1
  map6 := ((formed s).1 ⟨3,by decide⟩).1
  unheld5 := GeneralBorrowForestTagHighWater.get_none _ _ (((formed s).1 ⟨2,by decide⟩).2.2.2)
  unheld6 := GeneralBorrowForestTagHighWater.get_none _ _ (((formed s).1 ⟨3,by decide⟩).2.2.2)
  rootDifferent5 := Ne.symm (root_different s ⟨2,by decide⟩)
  rootDifferent6 := Ne.symm (root_different s ⟨3,by decide⟩)
  exprDifferent5 := future_different s ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide)
  exprDifferent6 := future_different s ⟨0,by decide⟩ ⟨3,by decide⟩ (by decide)
  helperDifferent5 := future_different s ⟨1,by decide⟩ ⟨2,by decide⟩ (by decide)
  helperDifferent6 := future_different s ⟨1,by decide⟩ ⟨3,by decide⟩ (by decide)
  different56 := future_different s ⟨2,by decide⟩ ⟨3,by decide⟩ (by decide)
  slotRootDifferent5 := slot_root_future s.tracker (chain s) s.slotRoot s.slotBelow ⟨2,by decide⟩
  slotRootDifferent6 := slot_root_future s.tracker (chain s) s.slotRoot s.slotBelow ⟨3,by decide⟩
  slotChildDifferent5 := slot_different s ⟨2,by decide⟩
  slotChildDifferent6 := slot_different s ⟨3,by decide⟩
}

end
end DuplicatePrefix.GeneralBorrowForestRawAllCountInput
