import duplicate_prefix.GeneralBorrowPositiveWildcardSharedCallPrefix
import duplicate_prefix.GeneralBorrowScopedRootZeroPhysical
import duplicate_prefix.GeneralBorrowScopedResourcesReturnPlan
import duplicate_prefix.GeneralBorrowScopedDefaultReleaseActivity
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardOriginalInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
set_option autoImplicit false in
/-- Original wildcard caller and initial graph/storage/configuration metadata.
No post-entry ownership, resource record or operation outcome is a field. -/
structure Base where
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
  len : UInt64
  count : UInt64
  nonzero : base ≠ 0
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  positive : (0 : UInt64) < len
  signedFits : len.toNat < 9223372036854775808
  bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat
  before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  ghost : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  enabled : before.borrowTracker = some tracker
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  position : Nat
  positionValid : position < before.user.addresses.intToPtrMap.size
  ordered : WildcardInteriorHitAddress.Ordered before.user.addresses.intToPtrMap
  addressRow : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩
  addressMode : before.user.addresses.provenanceMode ≠ .strict
  exposedAlloc : before.user.addresses.exposed.contains id = true
  location : LocationTree
  head : UniIndex
  headNode : TreeNode
  extraRoots : List UniIndex
  nodes : UniIndex → TreeNode
  states : UniIndex → Tree.LocationState
  locations : entry.allocation.extra.locations = RangeMapNonempty.homogeneous len location
  roots : entry.allocation.extra.roots = (head::extraRoots).toArray
  headPresent : entry.allocation.extra.nodes.get head = some headNode
  headLeaf : headNode.children = #[]
  headExposed : headNode.isExposed = true
  headStored : location.perms.get head = some GeneralBorrowWildcardLeaf.unique
  coherent : GeneralBorrowExposureCardinality.LocationCoherent entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
  short : entry.allocation.extra.nodes.size < 65536
  data : ∀ root ∈ extraRoots, entry.allocation.extra.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧ location.perms.get root = some (states root) ∧
      GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags root (nodes root)) .Read = true
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
  bufferSize : entry.allocation.byteSize = Size.ofBytes len
  mapAligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size
  nodeRoom : entry.allocation.extra.nodes.size+8 < 65536
  scope : ∀ index,area.support index ↔ index ∈ head::extraRoots
  allLeaves : ∀ root ∈ head::extraRoots, ∃ node,entry.allocation.extra.nodeAt root = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
      location.perms.get root = some GeneralBorrowWildcardLeaf.unique ∧ node.tag.value ≤ tracker.global.nextPointerTag.value
  slotTagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (GeneralBorrowPositiveWildcardFunctionState.next tracker fresh).global.nextPointerTag
  sharedTagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (GeneralBorrowPositiveWildcardFunctionState.held tracker fresh slotFresh).global.nextPointerTag
  slotTagDifferent : tracker.global.nextPointerTag ≠ (GeneralBorrowPositiveWildcardFunctionState.next tracker fresh).global.nextPointerTag
  sharedTagDifferent : tracker.global.nextPointerTag ≠ (GeneralBorrowPositiveWildcardFunctionState.held tracker fresh slotFresh).global.nextPointerTag
  sharedFresh : (GeneralBorrowPositiveWildcardFunctionState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
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

end
end DuplicatePrefix.GeneralBorrowPositiveWildcardOriginalInput
