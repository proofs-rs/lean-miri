import duplicate_prefix.GenericFunctionEntryCommon
import duplicate_prefix.GenericFunctionEntryRejected
import duplicate_prefix.GenericFunctionEntryRejectedPool
namespace DuplicatePrefix.GenericFunctionEntryCommonRejected
open Miri
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- The rejected numeric branch uses only the first two reserved future tags
and slots from the common original-caller contract. -/
def to_rejected_base (s : GenericFunctionEntryCommon.Base) (count : UInt64)
    (positive : (0 : UInt64)<count) (rejected : count>s.len/2) :
    GenericFunctionEntryRejected.InitialBase := {
  options := s.options
  limits := s.limits
  remaining := s.remaining
  span := s.span
  ctx := s.ctx
  debugOff := s.debugOff
  cmp := s.cmp
  dynamicFuel := s.dynamicFuel
  validityFuel := s.validityFuel
  fuelEq := s.fuelEq
  validationEq := s.validationEq
  id := s.id
  parentTag := s.parentTag
  tracker := s.tracker
  base := s.base
  offset := s.offset
  len := s.len
  nonzero := s.nonzero
  entry := s.entry
  positive := s.positive
  signedFits := s.signedFits
  bounds := s.bounds
  before := s.before
  ghost := s.ghost
  shallow := s.shallow
  cachedAddress := s.cachedAddress
  present := s.present
  enabled := s.enabled
  fresh := s.fresh
  data := s.data
  capacity := s.capacity
  race := s.race
  metadata := s.metadata
  notConstructed := s.notConstructed
  retagCtx := s.retagCtx
  place := s.place
  layout := s.layout
  slotId := s.slotId
  slotEntry := s.slotEntry
  slotBase := s.slotBase
  slotRoot := s.slotRoot
  slotPointer := s.slotPointer
  aligned := s.aligned
  slotCached := s.slotCached
  slotTree := s.slotTree
  slotSize := s.slotSize
  slotPresent := s.slotPresent
  separate := s.separate
  slotFresh := s.slotFresh
  slotDistinct := s.slotDistinct
  slotParentDistinct := s.slotParentDistinct
  slotFree := s.slotFree
  mutable := s.mutable
  storage := s.storage
  maskLength := s.maskLength
  provenance := s.provenance
  noBackend := s.noBackend
  extras := s.extras
  thread := s.thread
  active := s.active
  noCache := s.noCache
  source := s.source
  mode := s.mode
  unchecked := s.unchecked
  noGc := s.noGc
  fixed := s.fixed
  clean := s.clean
  successorFresh := s.successorFresh
  successorDifferent := s.successorDifferent
  writeContext := s.writeContext
  validationContext := s.validationContext
  accessEq := s.accessEq
  validationWidth := s.validationWidth
  validationRuntimeSize := s.validationRuntimeSize
  sameRuntime := s.sameRuntime
  width := s.width
  runtimeWidth := s.runtimeWidth
  runtimeSize := s.runtimeSize
  outerAccessEq := s.outerAccessEq
  slotFits := s.slotFits
  count := count
  countPositive := positive
  rejected := rejected
  budget := s.budget
  dispatchFuel := s.dispatchFuel
  precise := s.precise
  implicitWrites := s.implicitWrites
  exprFresh := s.exprFresh
  helperFresh := s.helperFresh
  futureMap := by
    intro index
    rcases index with ⟨index,valid⟩
    have h := s.futureMap ⟨index,by omega⟩
    have cases : index=0 ∨ index=1 := by omega
    rcases cases with rfl | rfl <;> exact h
  futureNodes := by
    intro index
    rcases index with ⟨index,valid⟩
    have h := s.futureNodes ⟨index,by omega⟩
    have cases : index=0 ∨ index=1 := by omega
    rcases cases with rfl | rfl <;> exact h
  exprUnheldInitial := s.futureUnheld ⟨0,by decide⟩ (Or.inl rfl)
  slotRootHelper := s.slotRootFuture ⟨1,by decide⟩ (by decide) }
/-- Legacy allocator wrapper for the rejected numeric branch. -/
def to_rejected {reuse : Bool} (s : GenericFunctionEntryCommon.Input reuse) (count : UInt64)
    (positive : (0 : UInt64)<count) (rejected : count>s.len/2) :
    GenericFunctionEntryRejected.Initial reuse := {
  toInitialBase := to_rejected_base s.toBase count positive rejected
  noFree := s.noFree
  roomShared := by change s.entry.allocation.extra.tagMapping.mapping.size+2 ≤ 4294967295;have h:=s.roomFour;omega
  futureClean := fun index => s.futureClean ⟨index.val,by have h:=index.isLt;omega⟩ }

/-- The rejected arbitrary-pool contract comes from the same initial caller,
without requiring initialized copy source bytes on this branch. -/
def to_rejected_pool (s : GenericFunctionEntryCommon.PoolInput) (count : UInt64)
    (positive : (0 : UInt64)<count) (rejected : count>s.len/2) :
    GenericFunctionEntryRejectedPool.Initial := {
  toInitialBase := to_rejected_base s.toBase count positive rejected
  pool := s.pool,accounting := s.accounting,nodeRoom := s.nodeRoom,cleanVacant := s.cleanVacant }

end
end DuplicatePrefix.GenericFunctionEntryCommonRejected
