import duplicate_prefix.GeneralBorrowForestAllCountSafety
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowResources
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionCaller
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- Physical memory, compiler/runtime configuration and finite numeric resources
for invoking the original function after a generated sibling lifecycle.
Borrow graph, ownership, caches, sparse allocator, vacant permissions, map
freshness and protector cleanup are formed from the source history separately. -/
structure Caller (tree : BorrowTree) (global : TreeBorrows.GlobalState) (bytes : UInt64) where
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
  signedFits : len.toNat < 9223372036854775808
  before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  ghost : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  enabled : before.borrowTracker = some tracker
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
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
  count : UInt64
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  fresh3 : (held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  fresh4 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag.value < 18446744073709551615
  statementFuel : limits.validation = validityFuel+1
  rootExprDifferent : tracker.global.nextPointerTag ≠ (held tracker fresh slotFresh).global.nextPointerTag
  rootHelperDifferent : tracker.global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag
  storageBuffer : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValidBuffer : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLengthBuffer : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initializedBuffer : count ≤ len/2 → InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenanceBuffer : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFitsBuffer : entry.allocation.len+64 < 18446744073709551616
  mutableBuffer : entry.allocation.mutability = .Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ len/2 → count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  fresh5 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag.value < 18446744073709551615
  fresh6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag.value < 18446744073709551615
  rootDifferent5 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag ≠ tracker.global.nextPointerTag
  rootDifferent6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag ≠ tracker.global.nextPointerTag
  exprDifferent5 : (held tracker fresh slotFresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  exprDifferent6 : (held tracker fresh slotFresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  helperDifferent5 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  helperDifferent6 : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  different56 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag ≠
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  slotRootDifferent5 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag ≠ slotRoot
  slotRootDifferent6 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag ≠ slotRoot
  slotChildDifferent5 : (next tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4).global.nextPointerTag
  slotChildDifferent6 : (next tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) fresh3) fresh4) fresh5).global.nextPointerTag
  idEq : id = GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation
  treeEq : entry.allocation.extra = tree
  globalEq : tracker.global = global
  parentEq : parentTag = BorTag.one
  offsetEq : offset = 0
  lenEq : len = bytes
  byteSizeEq : entry.allocation.byteSize = Size.ofBytes bytes
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionCaller
