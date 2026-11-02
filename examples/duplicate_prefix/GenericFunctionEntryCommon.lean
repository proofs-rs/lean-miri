import duplicate_prefix.GenericFunctionEntryZero
import duplicate_prefix.GenericFunctionEntryAccepted
import duplicate_prefix.PositiveRootCopyBounds
import duplicate_prefix.GenericFunctionEntryAcceptedPool
namespace DuplicatePrefix.GenericFunctionEntryCommon
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryAccepted
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

set_option autoImplicit false in
/-- Count-independent original positive-length caller, physical storage and
future-tag resources. Allocator policies are layered separately by the legacy
and arbitrary-pool inputs below. This is an explicit single-root contract,
not a classification of all valid Rust borrowing histories. -/
structure Base extends GenericFunctionEntryZero.Initial where
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  precise : options.retag.preciseInteriorMut = false
  implicitWrites : options.retag.implicitWrites = false
  statementFuel : limits.validation = validityFuel+1
  exprFresh : (seed tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  helperFresh : (stage1 tracker fresh slotFresh exprFresh).global.nextPointerTag.value < 18446744073709551615
  mutFresh : (stage2 tracker fresh slotFresh exprFresh helperFresh).global.nextPointerTag.value < 18446744073709551615
  mutEntryFresh : (stage3 tracker fresh slotFresh exprFresh helperFresh mutFresh).global.nextPointerTag.value < 18446744073709551615
  futureMap : ∀ index : Fin 4, GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (futureTags tracker fresh slotFresh exprFresh helperFresh mutFresh index)
  futureNodes : ∀ index : Fin 4, GeneralBorrowProtector.Fresh entry.allocation.extra
    (futureTags tracker fresh slotFresh exprFresh helperFresh mutFresh index)
  futureUnheld : ∀ index : Fin 4, index.val = 0 ∨ index.val = 2 → tracker.global.protectedTags.contains
    (futureTags tracker fresh slotFresh exprFresh helperFresh mutFresh index) = false
  slotRootFuture : ∀ index : Fin 4, 1 ≤ index.val →
    futureTags tracker fresh slotFresh exprFresh helperFresh mutFresh index ≠ slotRoot
  bufferStorage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  bufferMaskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  bufferMaskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize
  bufferInitialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+len))
  bufferProvenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  bufferStorageFits : entry.allocation.len+64 < 18446744073709551616
  bufferMutable : entry.allocation.mutability = .Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  lenBounded : len ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes


set_option autoImplicit false in
/-- Legacy empty-or-singleton allocator resources. -/
structure Input (reuse : Bool := false) extends Base where
  noFree : GenericFunctionEntryAllocatorChoice.Premise reuse entry.allocation.extra
  roomFour : entry.allocation.extra.tagMapping.mapping.size+4 ≤ 4294967295
  futureClean : ∀ step : Fin 4, GeneralBorrowFreshFutureClean.Clean entry.allocation.extra
    ⟨UInt32.ofNat (entry.allocation.extra.tagMapping.mapping.size+(step.val+1))⟩

set_option autoImplicit false in
/-- Count-independent original caller resources with arbitrary coherent free
pools and separate permission cleanliness for every initially vacant slot. -/
structure PoolInput extends Base where
  pool : GeneralBorrowFreshAllocatorInvariant.Pool entry.allocation.extra.nodes entry.allocation.extra.tagMapping.deassigned
  accounting : GeneralBorrowFreshStagePool.Accounting entry.allocation.extra
  nodeRoom : entry.allocation.extra.nodes.size+4 ≤ 4294967295
  cleanVacant : ∀ query, entry.allocation.extra.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean entry.allocation.extra query

/-- The accepted arithmetic guard bounds both the count and the copied source
prefix. Physical slice bounds exclude wrapping of either endpoint. -/
theorem prefix_bounds (offset len count capacity : UInt64)
    (within : count≤len/2) (bounds : offset.toNat+len.toNat≤capacity.toNat) :
    count≤len ∧ (offset+count).toNat≤(offset+len).toNat := by
  have guarded := PositiveRootCopyBounds.guarded len count offset capacity within bounds
  have capacityFits : capacity.toNat < 2^64 := UInt64.toNat_lt_size capacity
  have wholeFits : offset.toNat+len.toNat < 2^64 := by omega
  have prefixFits : offset.toNat+count.toNat < 2^64 := by omega
  refine ⟨UInt64.le_iff_toNat_le.mpr (by omega),?_⟩
  simp only [UInt64.toNat_add,Nat.mod_eq_of_lt wholeFits,Nat.mod_eq_of_lt prefixFits]
  omega

/-- Initialization of the input slice supplies every accepted copy prefix. -/
theorem initialized_prefix (mask : InitMask) (offset len count capacity : UInt64)
    (initialized : InitMaskCopy.InitializedOn mask (Size.ofBytes offset) (Size.ofBytes (offset+len)))
    (within : count≤len/2) (bounds : offset.toNat+len.toNat≤capacity.toNat) :
    InitMaskCopy.InitializedOn mask (Size.ofBytes offset) (Size.ofBytes (offset+count)) := by
  have finishBound := (prefix_bounds offset len count capacity within bounds).2
  cases blocks : mask.blocks with
  | Lazy state => simpa only [InitMaskCopy.InitializedOn,blocks] using initialized
  | Materialized materialized =>
    simp only [InitMaskCopy.InitializedOn,blocks] at initialized ⊢
    intro block valid bit small lower upper
    exact initialized block valid bit small lower (Nat.lt_of_lt_of_le upper finishBound)

/-- Forget only the count-independent extra resources for the zero branch. -/
def to_zero {reuse : Bool} (s : Input reuse) : GenericFunctionEntryZero.Initial := s.toBase.toInitial

/-- Build every accepted-path premise from the same original caller data and
the numeric branch condition. No operation outcome or family of branch Inputs
is an external assumption. -/
def to_accepted_base (s : Base) (count : UInt64) (positive : (0 : UInt64)<count) (within : count≤s.len/2) :
    GenericFunctionEntryAccepted.InitialBase := {
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
  count := count
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
  countPositive := positive
  unchecked := s.unchecked
  noGc := s.noGc
  fixed := s.fixed
  clean := s.clean
  successorFresh := s.successorFresh
  successorDifferent := s.successorDifferent
  budget := s.budget
  dispatchFuel := s.dispatchFuel
  precise := s.precise
  implicitWrites := s.implicitWrites
  statementFuel := s.statementFuel
  within := within
  exprFresh := s.exprFresh
  helperFresh := s.helperFresh
  mutFresh := s.mutFresh
  mutEntryFresh := s.mutEntryFresh
  futureMap := s.futureMap
  futureNodes := s.futureNodes
  futureUnheld := s.futureUnheld
  slotRootFuture := s.slotRootFuture
  bufferStorage := s.bufferStorage
  bufferMaskValid := s.bufferMaskValid
  bufferMaskLength := s.bufferMaskLength
  bufferInitialized := initialized_prefix s.entry.allocation.initializationMask s.offset s.len count s.entry.allocation.byteSize.bytes
      s.bufferInitialized within s.bounds
  bufferProvenance := s.bufferProvenance
  bufferStorageFits := s.bufferStorageFits
  bufferMutable := s.bufferMutable
  bufferExtras := s.bufferExtras
  bounded := UInt64.le_iff_toNat_le.mpr (by
    have countLe := UInt64.le_iff_toNat_le.mp (prefix_bounds s.offset s.len count s.entry.allocation.byteSize.bytes within s.bounds).1
    have lenLe := UInt64.le_iff_toNat_le.mp s.lenBounded
    omega)
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
  slotFits := s.slotFits }

/-- Recover the legacy accepted contract from its original allocator resources. -/
def to_accepted {reuse : Bool} (s : Input reuse) (count : UInt64) (positive : (0 : UInt64)<count) (within : count≤s.len/2) :
    GenericFunctionEntryAccepted.Initial reuse := {
  toInitialBase := to_accepted_base s.toBase count positive within
  noFree := s.noFree
  roomFour := s.roomFour
  futureClean := s.futureClean }

/-- Form the accepted arbitrary-pool branch using only the numeric branch test. -/
def to_accepted_pool (s : PoolInput) (count : UInt64) (positive : (0 : UInt64)<count) (within : count≤s.len/2) :
    GenericFunctionEntryAcceptedPool.Initial := {
  toInitialBase := to_accepted_base s.toBase count positive within
  pool := s.pool, accounting := s.accounting, nodeRoom := s.nodeRoom, cleanVacant := s.cleanVacant }

/-- The zero branch needs only the original caller contract. -/
def pool_to_zero (s : PoolInput) : GenericFunctionEntryZero.Initial := s.toBase.toInitial

end
end DuplicatePrefix.GenericFunctionEntryCommon
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.GenericFunctionEntryCommon.to_zero,``DuplicatePrefix.GenericFunctionEntryCommon.to_accepted,
      ``DuplicatePrefix.GenericFunctionEntryCommon.prefix_bounds,
      ``DuplicatePrefix.GenericFunctionEntryCommon.initialized_prefix] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved common-caller dependency {dependency}"
