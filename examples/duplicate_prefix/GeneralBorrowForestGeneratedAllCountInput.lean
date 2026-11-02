import duplicate_prefix.GeneralBorrowForestGeneratedTagHistory
import duplicate_prefix.GeneralBorrowForestRawAllCountSafety
namespace DuplicatePrefix.GeneralBorrowForestGeneratedAllCountInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open ActualReferenceContext GenericFunctionEntryState
open GeneralBorrowForestGeneratedTagHistoryData
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

set_option autoImplicit false in
/-- Original physical caller data bound to a real source-generated component
history. Neither its high-water invariant nor allocator certificate is an
input: both are formed by the actual seed and reached raw history guards.
Remaining permission/activity/physical-MIR conditions are still explicit. -/
structure Initial extends toOriginal : GeneralBorrowForestFunctionEntryZero.Initial where
  count : UInt64
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  statementFuel : limits.validation = validityFuel+1
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

  slotBelow : slotRoot.value.toNat < tracker.global.nextPointerTag.value.toNat
  tagRoom : tracker.global.nextPointerTag.value.toNat+6 ≤ 18446744073709551615
  historyId : AllocId
  historySize : Size
  historyTracked : Array BorTag
  events : List Event
  historySchedule : GeneralBorrowForestGeneratedTagHistory.Schedule historyId
    (GeneralBorrowForestGeneratedTagHistoryData.initial historyId historySize historyTracked) events
  historyCount : Nat
  treeHistory : entry.allocation.extra=(GeneralBorrowForestGeneratedTagHistory.run historyId
    (GeneralBorrowForestGeneratedTagHistoryData.initial historyId historySize historyTracked) (events.take historyCount)).state.tree
  globalHistory : tracker.global=(GeneralBorrowForestGeneratedTagHistory.run historyId
    (GeneralBorrowForestGeneratedTagHistoryData.initial historyId historySize historyTracked) (events.take historyCount)).state.global

theorem formed (s : Initial) : Invariant (GeneralBorrowForestGeneratedTagHistory.run s.historyId
    (GeneralBorrowForestGeneratedTagHistoryData.initial s.historyId s.historySize s.historyTracked) (s.events.take s.historyCount)).state :=
  (GeneralBorrowForestGeneratedTagHistory.from_seed s.historyId s.historySize s.historyTracked s.events s.historySchedule s.historyCount).2.1

theorem high_water (s : Initial) : GeneralBorrowForestTagHighWater.Below s.entry.allocation.extra s.tracker.global.protectedTags s.tracker.global.nextPointerTag := by
  have bound := (formed s).below
  rw [←s.treeHistory,←s.globalHistory] at bound
  exact bound

theorem allocator (s : Initial) : GeneralBorrowGcAllocator.Invariant s.entry.allocation.extra := by
  rw [s.treeHistory]
  exact (formed s).structural.allocator

def toRaw (s : Initial) : GeneralBorrowForestRawAllCountInput.Initial := {
  toOriginal := s.toOriginal
  count := s.count
  preciseOff := s.preciseOff
  implicitOff := s.implicitOff
  budget := s.budget
  dispatchFuel := s.dispatchFuel
  statementFuel := s.statementFuel
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
  slotBelow := s.slotBelow
  tagRoom := s.tagRoom
  allocator := allocator s
  highWater := high_water s
}

end
end DuplicatePrefix.GeneralBorrowForestGeneratedAllCountInput
