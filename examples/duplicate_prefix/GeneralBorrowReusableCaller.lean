import duplicate_prefix.GeneralBorrowReusableStar
import duplicate_prefix.GenericFunctionEntryCommon
namespace DuplicatePrefix.GeneralBorrowReusableCaller
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState GenericFunctionEntryAccepted
open Miri.DataStructures Miri.TreeBorrows.Tree
open GeneralBorrowReusableStar
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

set_option autoImplicit false in
/-- External physical caller, storage, compiler metadata, fuel and tag-number
resources. Borrow graph, ownership, allocator, vacant permissions and fresh-node
contracts are deliberately derived by the factory, rather than fields here.
The protected-tag map is empty in this scoped generation protocol. -/
structure Caller (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (state : State tree root bytes) (tag : BorTag) (reserve : Fin 5 → BorTag) where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  ctx : Context options remaining span
  debugOff : options.place.debugAssertions = false
  cmp : ProjectionMetadataFacts.NullComparator
  dynamicFuel : Nat
  validityFuel : Nat
  fuelEq : options.place.dynamicFuel = dynamicFuel+1
  validationEq : options.limits.validation = validityFuel+1
  id : AllocId
  parentTag : BorTag
  tracker : MachineHooks.BorrowState
  base : UInt64
  offset : UInt64
  len : UInt64
  nonzero : base+offset ≠ 0
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  positive : (0 : UInt64) < len
  signedFits : len.toNat < 9223372036854775808
  bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat
  before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  ghost : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  enabled : before.borrowTracker = some tracker
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize
  race : before.dataRace = none
  metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
  retagCtx : ActualRetagContext.Context options (remaining+1) span
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotId : AllocId
  slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotBase : UInt64
  slotRoot : BorTag
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  slotCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1)
  slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1
  slotPresent : before.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry)
  separate : slotId ≠ id
  slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615
  slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh
  slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag
  mutable : slotEntry.allocation.mutability = .Mut
  storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat
  maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize
  provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new
  noBackend : before.user.payload.payload.user.backend = .none
  extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  thread : Miri.Concurrency.ThreadRecord
  active : before.threads.activeThread? = some thread
  noCache : thread.topUserRelevantFrame = none
  source : PreparedContracts.SourceComparator
  mode : tracker.retagMode = .Default
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0
  fixed : before.threads.fixedScheduling = true
  successorDifferent : tracker.global.nextPointerTag ≠ (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag
  writeContext : PhysicalMachineWrite.Context
  validationContext : PhysicalMachineWrite.Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = writeContext.access.runtime.base
  width : writeContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : writeContext.access.runtime.base.pointerWidth = .w64
  runtimeSize : writeContext.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = writeContext.access
  slotFits : slotBase.toNat+1 < 2^64
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  precise : options.retag.preciseInteriorMut = false
  implicitWrites : options.retag.implicitWrites = false
  statementFuel : limits.validation = validityFuel+1
  exprFresh : (seed tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  helperFresh : (stage1 tracker fresh slotFresh exprFresh).global.nextPointerTag.value < 18446744073709551615
  mutFresh : (stage2 tracker fresh slotFresh exprFresh helperFresh).global.nextPointerTag.value < 18446744073709551615
  mutEntryFresh : (stage3 tracker fresh slotFresh exprFresh helperFresh mutFresh).global.nextPointerTag.value < 18446744073709551615
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
  treeEq : entry.allocation.extra = tree
  parentEq : parentTag = state.node.tag
  nextTagEq : tracker.global.nextPointerTag = tag
  offsetEq : offset = 0
  lenEq : len = bytes
  protectedEmpty : tracker.global.protectedTags = {}
  successorReserved : reserve 0 = (next tracker fresh).global.nextPointerTag
  futureReserved : ∀ step : Fin 4, reserve step.succ = futureTags tracker fresh slotFresh exprFresh helperFresh mutFresh step

/-- Construct the complete pooled initial contract from recurring borrow facts
and the separate physical caller conditions. No operation-success input. -/
def pool (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (state : State tree root bytes) (tag : BorTag)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ index, GeneralBorrowTagMap.Fresh tree.tagMapping (reserve index))
    (s : Caller tree root bytes state tag reserve) :
    GenericFunctionEntryCommon.PoolInput := by
  let entryData : GenericAsMutPtrEntryValidity.Data s.entry.allocation.extra s.tracker.global.protectedTags
      s.parentTag s.tracker.global.nextPointerTag s.offset s.len := by
    rw [s.treeEq,s.protectedEmpty,s.parentEq,s.nextTagEq,s.offsetEq,s.lenEq]
    exact GeneralBorrowReusableStar.data tree root bytes state tag freshTag
  have clean : ∀ query, s.entry.allocation.extra.nodes.get query = none →
      GeneralBorrowFreshFutureClean.Clean s.entry.allocation.extra query := by
    rw [s.treeEq]
    intro query vacant position valid
    have zero : position = 0 := by rw [state.locations] at valid;change position < 1 at valid;omega
    subst position
    simpa only [state.locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using state.profile.vacant query vacant
  refine {
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
    budget := s.budget
    dispatchFuel := s.dispatchFuel
    precise := s.precise
    implicitWrites := s.implicitWrites
    statementFuel := s.statementFuel
    exprFresh := s.exprFresh
    helperFresh := s.helperFresh
    mutFresh := s.mutFresh
    mutEntryFresh := s.mutEntryFresh
    slotRootFuture := s.slotRootFuture
    bufferStorage := s.bufferStorage
    bufferMaskValid := s.bufferMaskValid
    bufferMaskLength := s.bufferMaskLength
    bufferInitialized := s.bufferInitialized
    bufferProvenance := s.bufferProvenance
    bufferStorageFits := s.bufferStorageFits
    bufferMutable := s.bufferMutable
    bufferExtras := s.bufferExtras
    lenBounded := s.lenBounded
    data := entryData
    clean := clean _ (GeneralBorrowFreshMutableStages.slot_vacant _ _ _ entryData.slot)
    slotFree := by rw [s.protectedEmpty];rfl
    successorFresh := by
      rw [s.treeEq,←s.successorReserved]
      exact GeneralBorrowFullSharedResources.protector_fresh tree state.allocator.nodeTags (reserve 0) (reserved 0)
    futureMap := by
      intro step
      rw [s.treeEq,←s.futureReserved step]
      exact reserved step.succ
    futureNodes := by
      intro step
      rw [s.treeEq,←s.futureReserved step]
      exact GeneralBorrowFullSharedResources.protector_fresh tree state.allocator.nodeTags (reserve step.succ) (reserved step.succ)
    futureUnheld := by intro step _;rw [s.protectedEmpty];rfl
    pool := by rw [s.treeEq];exact state.allocator.pool
    accounting := by rw [s.treeEq];exact state.allocator.accounting
    nodeRoom := by rw [s.treeEq];exact state.room
    cleanVacant := clean
  }
end
end DuplicatePrefix.GeneralBorrowReusableCaller
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowReusableCaller.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated physical caller dependency {dependency}"
