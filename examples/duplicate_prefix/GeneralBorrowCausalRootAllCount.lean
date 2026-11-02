import duplicate_prefix.GeneralBorrowRawRootAllCount
import duplicate_prefix.GeneralBorrowCausalGraphFormation
namespace DuplicatePrefix.GeneralBorrowCausalRootAllCount
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- Existing raw FnEntry data with ONLY the explicit conditional order field
removed. This record is not called ValidCaller. -/
structure BorrowInput (tree : BorrowTree) (global : Miri.TreeBorrows.GlobalState) where
  parentTag : BorTag
  parent : UniIndex
  selected : UniIndex
  maximum : Option BorTag
  offset : UInt64
  len : UInt64
  tagged : tree.indexOfTag parentTag = some parent
  positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
    (some parent) (some selected) maximum offset len
  distinct : tree.roots.toList.Nodup
  short : tree.nodes.size < 65536
  nodeRoom : tree.nodes.size+1 ≤ 4294967295
  tagRoom : global.nextPointerTag.value < 18446744073709551615

/-- Same normalized physical/configuration/resource interface as the checked
concrete all-count Initial. Raw borrow data contains no order assumption.
Causal graph formation is supplied separately to invoke; exhaustive ordinary
valid-state coverage of that evidence remains a separate obligation. -/
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
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global
  raw : BorrowInput entry.allocation.extra tracker.global
  rawTag : raw.parentTag = parentTag
  rawOffset : raw.offset = offset
  rawLen : raw.len = len
  nodeHeadroom : entry.allocation.extra.nodes.size+1 < 65536
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


private def restore (s : Initial) (formed : GeneralBorrowCausalGraphFormation.Formed s.entry.allocation.extra) :
    GeneralBorrowRawRootZeroEntry.Initial := {
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
  runtime := s.runtime
  raw := {
    parentTag := s.raw.parentTag
    parent := s.raw.parent
    selected := s.raw.selected
    maximum := s.raw.maximum
    offset := s.raw.offset
    len := s.raw.len
    tagged := s.raw.tagged
    positive := s.raw.positive
    distinct := s.raw.distinct
    short := s.raw.short
    nodeRoom := s.raw.nodeRoom
    tagRoom := s.raw.tagRoom
    order := fun _ _ => GeneralBorrowCausalGraphFormation.order formed }
  rawTag := s.rawTag
  rawOffset := s.rawOffset
  rawLen := s.rawLen
  nodeHeadroom := s.nodeHeadroom
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
}

/-- Actual original concrete call/return and finite-prefix NoUB for EVERY
count, deriving order from count-independent graph formation. No target
operation success, future permission or safety assumption is used. This is a
generated-state family, NOT all-valid-input or S02 completion. -/
theorem invoke (s : Initial)
    (formed : GeneralBorrowCausalGraphFormation.Formed s.entry.allocation.extra)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615)
    (bytes : GeneralBorrowRawSliceBytes.Data s.entry.allocation s.offset s.len)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation = s.validityFuel+1) (n : UInt64) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset)))) s.len n s.place := by
  exact GeneralBorrowRawRootAllCount.invoke (restore s formed) preciseOff implicitOff budget dispatch nodeMargin tagMargin bytes bufferExtras statementFuel n
end
end DuplicatePrefix.GeneralBorrowCausalRootAllCount
