import duplicate_prefix.GeneralBorrowPositiveWildcardFamilyTags
import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyRows
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Physical caller/compiler/storage data only. Borrow rows, caches, graph
history, tag-map freshness and initial protection flags are supplied by the
source-generated root family rather than requested here. -/
structure Caller (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) where
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
  tracker : MachineHooks.BorrowState
  base : UInt64
  count : UInt64
  nonzero : base ≠ 0
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  signedFits : capacity.toNat < 9223372036854775808
  before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  ghost : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  enabled : before.borrowTracker = some tracker
  position : Nat
  positionValid : position < before.user.addresses.intToPtrMap.size
  ordered : WildcardInteriorHitAddress.Ordered before.user.addresses.intToPtrMap
  addressRow : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩
  addressMode : before.user.addresses.provenanceMode ≠ .strict
  exposedAlloc : before.user.addresses.exposed.contains id = true
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
  bufferSize : entry.allocation.byteSize = Size.ofBytes capacity
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
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
  trackerGlobal : tracker.global=global
  entryTree : entry.allocation.extra=tree
  tagRoom : tracker.global.nextPointerTag.value.toNat+6≤18446744073709551615
  nodeRoom : tree.nodes.size+8<65536
  slotNotSuccessor : slotRoot.value.toNat≠tracker.global.nextPointerTag.value.toNat+1
  statementFuel : limits.validation=validityFuel+1
  budget : Nat
  dispatchFuel : limits.callDispatch=budget+1
  bufferStorage : entry.allocation.len=entry.allocation.byteSize.bytes.toNat
  bufferMaskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  bufferMaskLength : entry.allocation.initializationMask.len=entry.allocation.byteSize
  bufferInitialized : (0 : UInt64)<count→count≤capacity/2→InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes 0) (Size.ofBytes count)
  bufferProvenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  bufferStorageFits : (0 : UInt64)<count→count≤capacity/2→entry.allocation.len+64<18446744073709551616
  bufferMutable : entry.allocation.mutability=.Mut
  bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id)=some (id,⟨none,#[]⟩)

def scope (roots : List UniIndex) : GeneralBorrowExposedKnownRootState.Scope := ⟨fun index=>index∈roots⟩
def tags {capacity global tree} (p : Caller capacity global tree) : GeneralBorrowPositiveWildcardFamilyTags.Plan p.tracker p.id :=
  Classical.choice (GeneralBorrowPositiveWildcardFamilyTags.make p.tracker p.id p.tagRoom)
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardFamilyPhysical
