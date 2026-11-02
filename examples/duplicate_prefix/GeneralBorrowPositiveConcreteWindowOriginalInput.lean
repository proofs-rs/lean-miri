import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowLayout
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseFunctionInvocation
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseFunctionState
import duplicate_prefix.GeneralBorrowScopedRootZeroPhysical
import duplicate_prefix.GeneralBorrowScopedResourcesReturnPlan
import duplicate_prefix.GeneralBorrowScopedDefaultReleaseActivity
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowOriginalInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
set_option autoImplicit false in
/-- Original concrete selected-parent caller and initial graph/storage/configuration metadata.
The cached allocation base and capacity remain distinct from the slice offset
and length. No post-entry ownership, resource or operation outcome is a field. -/
structure BaseFor (profileMode : ProfileMode) where
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
  selected : UniIndex
  tracker : MachineHooks.BorrowState
  base : UInt64
  capacity : UInt64
  offset : UInt64
  len : UInt64
  count : UInt64
  nonzero : base ≠ 0
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  positive : (0 : UInt64) < len
  signedFits : len.toNat < 9223372036854775808
  bounds : offset.toNat+len.toNat ≤ capacity.toNat
  addressFits : base.toNat+capacity.toNat<2^64
  before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  ghost : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  enabled : before.borrowTracker = some tracker
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  head : UniIndex
  extraRoots : List UniIndex
  roots : entry.allocation.extra.roots = (head::extraRoots).toArray
  short : entry.allocation.extra.nodes.size < 65536
  tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag
  noFree : entry.allocation.extra.tagMapping.deassigned.back? = none
  fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295
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
  slotFree : tracker.global.protectedTags.contains slotRoot = false
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
  initialState : GeneralBorrowStructuralHistoryState.State entry.allocation.extra
  bufferSize : entry.allocation.byteSize = Size.ofBytes capacity
  mapAligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size
  nodeRoom : entry.allocation.extra.nodes.size+8 < 65536
  scope : ∀ index,area.support index ↔ index ∈ head::extraRoots ∧ index≠selected
  data : GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw.DataFor entry.allocation.extra tracker.global.protectedTags
    parentTag tracker.global.nextPointerTag offset len selected head extraRoots profileMode
  slotTagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag
  sharedTagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag
  slotTagDifferent : tracker.global.nextPointerTag ≠ (GeneralBorrowPositiveWildcardSparseFunctionState.next tracker fresh).global.nextPointerTag
  sharedTagDifferent : tracker.global.nextPointerTag ≠ (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag
  sharedFresh : (GeneralBorrowPositiveWildcardSparseFunctionState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
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
  allocationCapacity : entry.allocation.extra.locations.size.bytes=capacity

/-- Existing public caller type retains its global permission contract. Window
callers use BaseFor .window explicitly; no window-to-global coercion exists. -/
abbrev Base := BaseFor .global

end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowOriginalInput
