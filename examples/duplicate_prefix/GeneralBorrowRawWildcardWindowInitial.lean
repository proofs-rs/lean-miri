import duplicate_prefix.GeneralBorrowFreshRootScopedWildcardHitBackendInput
import duplicate_prefix.GeneralBorrowRawRootZeroEntry
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowInitial
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- Count-independent normalized positive wildcard live-hit caller contract.
Exact-base and interior addresses share raw Geometry. No order, traversal-success,
future operation or safety conclusion is an input. Physical/configuration and
resource restrictions remain explicit; ordinary-valid-input coverage is separate. -/
structure Initial where
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
  address : UInt64
  base : UInt64
  len : UInt64
  nonzero : address ≠ 0
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  positive : (0 : UInt64) < len
  signedFits : len.toNat < 9223372036854775808
  bounds : (address-base).toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat
  before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  ghost : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  enabled : before.borrowTracker = some tracker
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap address base id entry.allocation.byteSize
  addressMode : before.user.addresses.provenanceMode ≠ .strict
  exposedAlloc : before.user.addresses.exposed.contains id = true
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global
  capability : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags none none none (address-base) len
  distinct : entry.allocation.extra.roots.toList.Nodup
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
  capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize
  nodeHeadroom : entry.allocation.extra.nodes.size+1 < 65536
  tagHeadroom : tracker.global.nextPointerTag.value.toNat+2 < 18446744073709551615
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

abbrev offset (s : Initial) : UInt64 := s.address-s.base
abbrev global (s : Initial) := GeneralBorrowRawWildcardWindowFunctionState.held s.tracker s.fresh s.slotFresh
noncomputable def adjusted (s : Initial) : Immediate Provenance :=
  (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes s.address)) s.len ActualReferenceMetadata.reference).imm
noncomputable def caller (s : Initial) (n : UInt64) : CompilerFrameContext.ActualFrame :=
  PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race) (adjusted s) n {} s.id
    s.tracker.global.nextPointerTag s.slotId (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag
noncomputable def machine (s : Initial) (output : GeneralBorrowForestFnEntry.Output)
    (slotAllocation : Allocation Provenance BorrowTree) : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  GeneralBorrowRawWildcardWindowFunctionState.enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry output.child.tree
    s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation

def ActualCall (s : Initial) (n : UInt64) (frame : CompilerFrameContext.ActualFrame)
    (entered : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop :=
  Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
    RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes s.address)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
      .Copy (EmptyRootArguments.second n)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
    .ok () (Storage.withCurrent #[] frame entered)

def SlotProperties (s : Initial) (allocation : Allocation Provenance BorrowTree) : Prop :=
  allocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (GeneralBorrowRawWildcardWindowFunctionState.next s.tracker s.fresh).global.nextPointerTag 1 true ∧
  allocation.byteSize = Size.ofBytes 1 ∧ allocation.len = 1 ∧
  allocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧ allocation.provenanceMap = ProvenanceMap.new ∧
  AllocationCopy.snapshot allocation = AllocationCopy.snapshot s.slotEntry.allocation ∧ allocation.mutability = .Mut
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowInitial
