import duplicate_prefix.GeneralBorrowFreshSharedNext
import duplicate_prefix.GeneralBorrowFreshStagePool
import duplicate_prefix.GenericAsMutDefaultReturn
namespace DuplicatePrefix.GenericSharedAcceptedInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option autoImplicit false in
/-- Initial PC2:11 physical, runtime, storage and future-tag data, independent
of how fresh node slots are selected. No post-state or successful operation is
supplied. Allocator-specific hygiene belongs to the thin input wrappers. -/
structure Base where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  span : PreparedContracts.FixedSpanQuery
  precise : options.retag.preciseInteriorMut = false
  implicitWrites : options.retag.implicitWrites = false
  debug : options.place.debugAssertions = false
  cmp : ProjectionMetadataFacts.NullComparator
  dynamicFuel : Nat
  validityFuel : Nat
  dynamicEq : options.place.dynamicFuel = dynamicFuel+1
  validationEq : options.limits.validation = validityFuel+1
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  len : UInt64
  positive : (0 : UInt64) < len
  nonnull : base+offset ≠ 0
  signedFits : len.toNat < 9223372036854775808
  frame : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracker : MachineHooks.BorrowState
  enabled : machine.borrowTracker = some tracker
  defaultMode : tracker.retagMode = .Default
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  target : UniIndex
  first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len
  capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize
  owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations
  fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615
  tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  v1 : 1 < frame.locals.size
  v11 : 11 < frame.locals.size
  v12 : 12 < frame.locals.size
  sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)
  sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference
  lenLive : frame.locals[11].value = .live (.immediate .uninit)
  lenUncached : frame.locals[11].layout = none
  exprLive : frame.locals[12].value = .live (.immediate .uninit)
  exprUncached : frame.locals[12].layout = none
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  location : frame.location = .mir ⟨2,11⟩
  frameRace : frame.extra.dataRace = none
  race : machine.dataRace = none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
  backend : machine.user.payload.payload.user.backend = .none
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread
  threadCache : thread.topUserRelevantFrame = some 0
  unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  source : PreparedContracts.SourceComparator
  rangePositive : offset.toNat < (offset+len).toNat
  exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false
  size : frame.locals.size=25
  count : UInt64
  countPositive : (0 : UInt64)<count
  within : count≤len/2
  all : CopyHelperCleanup.AllImmediate frame
  live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)
  cache0 : (frame.locals[0]'(by omega)).layout=none
  live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)
  cache7 : (frame.locals[7]'(by omega)).layout=none
  live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)
  cache8 : (frame.locals[8]'(by omega)).layout=none
  live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count))))
  cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout
  live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)
  cache10 : (frame.locals[10]'(by omega)).layout=none
  live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)
  cache13 : (frame.locals[13]'(by omega)).layout=none
  dead15 : (frame.locals[15]'(by omega)).value=.dead
  cache15 : (frame.locals[15]'(by omega)).layout=none
  dead16 : (frame.locals[16]'(by omega)).value=.dead
  cache16 : (frame.locals[16]'(by omega)).layout=none
  initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)
  statementFuel : limits.validation = validityFuel+1
  runtimeContext : ActualReferenceContext.Context options remaining span
  targetNotExposed : first.parentNode.isExposed = false
  trackNone : frame.trackCallerArg = none
  relevant : frame.extra.userRelevance > 0
  slot2 : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ index, 17 ≤ index → index ≤ 24 → frame.locals[index]? = some ⟨.dead,none⟩
  fresh3 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag.value < 18446744073709551615
  fresh4 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag.value < 18446744073709551615
  mapFresh3 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag
  nodeFresh3 : GeneralBorrowProtector.Fresh entry.allocation.extra
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag
  mapFresh4 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag
  nodeFresh4 : GeneralBorrowProtector.Fresh entry.allocation.extra
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag
  storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFits : entry.allocation.len+64 < 18446744073709551616
  mutable : entry.allocation.mutability = .Mut
  bufferExtras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  continuation : frame.returnContinuation = .stop true
  varargs : frame.vaList = #[]
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access
  slotId : AllocId
  separate : slotId ≠ id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = slotTree slotRoot slotChild 1 true
  slotRootFree : tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  frameTracked : frame.extra.borrowTracker = some
    ((({} : FrameState).addProtector id first.parentTag).addProtector slotId slotChild)
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  slotCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
  different23 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag
  different24 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag
  different34 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag
  unheld3 : tracker.global.protectedTags.contains
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag = false
  targetDifferent3 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag ≠ first.parentTag
  targetDifferent4 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag ≠ first.parentTag
  slotRootDifferent2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠ slotRoot
  slotChildDifferent2 : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  slotRootDifferent3 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag ≠ slotRoot
  slotChildDifferent3 : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2).global.nextPointerTag
  slotRootDifferent4 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag ≠ slotRoot
  slotChildDifferent4 : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh2) fresh3).global.nextPointerTag

set_option autoImplicit false in
/-- The original append-only contract, retained as a wrapper over common data. -/
structure Input extends Base where
  noFree : entry.allocation.extra.tagMapping.deassigned.back? = none
  room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295
  cleanFuture : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none) entry.allocation.extra.locations
  roomFour : entry.allocation.extra.tagMapping.mapping.size+3 ≤ 4294967295
  clean3 : GeneralBorrowFreshFutureClean.Clean entry.allocation.extra ⟨UInt32.ofNat (entry.allocation.extra.tagMapping.mapping.size+2)⟩
  clean4 : GeneralBorrowFreshFutureClean.Clean entry.allocation.extra ⟨UInt32.ofNat (entry.allocation.extra.tagMapping.mapping.size+3)⟩

set_option autoImplicit false in
/-- Initial arbitrary-pool data. Vacancy hygiene and conservative node capacity
are stated before either shared stage, not as intermediate execution premises. -/
structure PoolInput extends Base where
  pool : GeneralBorrowFreshAllocatorInvariant.Pool entry.allocation.extra.nodes entry.allocation.extra.tagMapping.deassigned
  accounting : GeneralBorrowFreshStagePool.Accounting entry.allocation.extra
  cleanVacant : ∀ query, entry.allocation.extra.nodes.get query = none →
    GeneralBorrowFreshFutureClean.Clean entry.allocation.extra query
  nodeRoom : entry.allocation.extra.nodes.size+3 ≤ 4294967295

instance : Coe Input Base := ⟨Input.toBase⟩
instance : Coe PoolInput Base := ⟨PoolInput.toBase⟩
end DuplicatePrefix.GenericSharedAcceptedInput
