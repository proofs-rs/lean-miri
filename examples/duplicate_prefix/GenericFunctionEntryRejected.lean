import duplicate_prefix.GenericFunctionEntryRuntime
import duplicate_prefix.GenericFunctionEntryNumerics
import duplicate_prefix.GenericFunctionEntryFullReady
import duplicate_prefix.GenericFunctionEntrySharedParent
import duplicate_prefix.GenericFunctionEntryAllocatorChoice
import duplicate_prefix.GenericSharedRejectedInput
namespace DuplicatePrefix.GenericFunctionEntryRejected
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
abbrev seed (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (slotFresh : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615) := held tracker fresh slotFresh
abbrev stage1 (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (slotFresh : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (exprFresh : (seed tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615) :=
  ReferenceBorrowDriver.allocatedTracker (seed tracker fresh slotFresh) exprFresh
abbrev futureTags (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (slotFresh : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (exprFresh : (seed tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615) (index : Fin 2) : BorTag :=
  if index.val=0 then (seed tracker fresh slotFresh).global.nextPointerTag else (stage1 tracker fresh slotFresh exprFresh).global.nextPointerTag
set_option autoImplicit false in
/-- Original caller/configuration and two-shared-stage data. Every premise
precedes genuine ROOT entry; the rejected path reserves no mutable-helper tags
or slots and assumes no initialized copy source or operation success. -/
structure InitialBase where
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
  data : GenericAsMutPtrEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len
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
  clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) entry.allocation.extra.locations
  successorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag
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
  countPositive : (0 : UInt64) < count
  rejected : count > len/2
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  precise : options.retag.preciseInteriorMut = false
  implicitWrites : options.retag.implicitWrites = false
  exprFresh : (seed tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  helperFresh : (stage1 tracker fresh slotFresh exprFresh).global.nextPointerTag.value < 18446744073709551615
  futureMap : ∀ index : Fin 2, GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (futureTags tracker fresh slotFresh exprFresh index)
  futureNodes : ∀ index : Fin 2, GeneralBorrowProtector.Fresh entry.allocation.extra
    (futureTags tracker fresh slotFresh exprFresh index)
  exprUnheldInitial : tracker.global.protectedTags.contains (seed tracker fresh slotFresh).global.nextPointerTag = false
  slotRootHelper : (stage1 tracker fresh slotFresh exprFresh).global.nextPointerTag ≠ slotRoot


set_option autoImplicit false in
/-- Legacy allocator resources layered over original caller data. -/
structure Initial (reuse : Bool := false) extends InitialBase where
  noFree : GenericFunctionEntryAllocatorChoice.Premise reuse entry.allocation.extra
  roomShared : entry.allocation.extra.tagMapping.mapping.size+2 ≤ 4294967295
  futureClean : ∀ step : Fin 2, GeneralBorrowFreshFutureClean.Clean entry.allocation.extra
    ⟨UInt32.ofNat (entry.allocation.extra.tagMapping.mapping.size+(step.val+1))⟩


/-- Form the shared/rejected contract while executing actual ROOT entry and the nonzero-count prefix. -/
theorem prepare_base (s : InitialBase)
    (first : GeneralBorrowFreshSharedSequence.Data
      (GenericAsMutPtrArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)
      (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag
      (GeneralBorrowFreshMutableStages.slot_index s.data.slot) s.offset s.len)
    (firstTag : first.parentTag = s.tracker.global.nextPointerTag)
    (firstNotExposed : first.parentNode.isExposed = false) :
    ∃ input : GenericSharedRejectedInput.Base,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      input.id=s.id ∧ input.count=s.count ∧ input.place=s.place ∧
      input.entry.allocation.extra = GenericAsMutPtrArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len ∧
      ∃ installed,
        Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
            (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
            ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
          ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
        SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
          (Storage.withCurrent #[] input.frame input.machine) ∧ installed.stack.frames.size=1 := by
  classical
  obtain ⟨slotAllocation,frame,call,trace,shape,ready,slotTree,slotSize,slotStorage,slotMask,slotProvenance,slotBytes,slotMutable,
      metadata,present,enabled,owned,activeWithin,future,futureClean⟩ := GenericFunctionEntrySharedBundle.enter
    s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.parentTag s.tracker s.base s.offset s.len s.count s.nonzero s.entry s.positive s.signedFits s.bounds s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh s.data s.capacity s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache s.source s.mode s.countPositive s.unchecked s.noGc s.fixed s.clean s.successorFresh s.successorDifferent
  let raw := RawRootInvocation.machine #[] s.before
  let entered := enteredMachine raw s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation
  let machine := RootZeroCompleteState.tick s.options s.remaining s.span entered
  let tree := GenericAsMutPtrArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation := s.entry.allocation.setExtra tree}
  let tracker := seed s.tracker s.fresh s.slotFresh
  let tag1 := stage1 s.tracker s.fresh s.slotFresh s.exprFresh
  let tags := futureTags s.tracker s.fresh s.slotFresh s.exprFresh
  have runtime := GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag
    s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed
  obtain ⟨thread,threadActive,threadCache⟩ := runtime.active
  have full := GenericFunctionEntryFullReady.from_shape s.before s.place s.race _ s.count s.id s.tracker.global.nextPointerTag
    s.slotId (next s.tracker s.fresh).global.nextPointerTag frame shape
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  have nonzero := UInt64.pos_iff_ne_zero.mp s.positive
  have growth0 := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
  have growth1 := GenericFunctionEntryNumerics.successor_value (next s.tracker s.fresh).global.nextPointerTag s.slotFresh
  have growth2 := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag s.exprFresh
  change (next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at growth0
  change tracker.global.nextPointerTag.value.toNat = (next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at growth1
  change tag1.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at growth2
  have ne (a b : BorTag) (less : a.value.toNat < b.value.toNat) : a ≠ b := by
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  have oldDifferent : ∀ index : Fin 2, s.tracker.global.nextPointerTag ≠ tags index := by
    intro index
    have cases : index.val=0 ∨ index.val=1 := by have h:=index.isLt;omega
    rcases cases with h | h
    · simpa only [tags,futureTags,h,ite_true] using ne s.tracker.global.nextPointerTag tracker.global.nextPointerTag (by omega)
    · simpa only [tags,futureTags,h,Nat.reduceEqDiff,ite_false] using ne s.tracker.global.nextPointerTag tag1.global.nextPointerTag (by omega)
  have childDifferent : ∀ index : Fin 2, (next s.tracker s.fresh).global.nextPointerTag ≠ tags index := by
    intro index
    have cases : index.val=0 ∨ index.val=1 := by have h:=index.isLt;omega
    rcases cases with h | h
    · simpa only [tags,futureTags,h,ite_true] using ne (next s.tracker s.fresh).global.nextPointerTag tracker.global.nextPointerTag (by omega)
    · simpa only [tags,futureTags,h,Nat.reduceEqDiff,ite_false] using ne (next s.tracker s.fresh).global.nextPointerTag tag1.global.nextPointerTag (by omega)
  have freshTags : ∀ index : Fin 2, GeneralBorrowTagMap.Fresh tree.tagMapping (tags index) ∧ GeneralBorrowProtector.Fresh tree (tags index) :=
    fun index => future (tags index) (s.futureMap index) (s.futureNodes index) (oldDifferent index)
  have v (index : Fin 25) : index.val < frame.locals.size := by rw [ready.size];exact index.isLt
  have row (index : Nat) (valid : index < frame.locals.size) (state : LocalState Provenance LocalLayout)
      (known : frame.locals[index]? = some state) : (frame.locals[index]'valid) = state :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)
  have r0 := row 0 (v ⟨0,by decide⟩) _ ready.slot0
  have r1 := row 1 (v ⟨1,by decide⟩) _ ready.source
  have r7 := row 7 (v ⟨7,by decide⟩) _ ready.slot7
  have r8 := row 8 (v ⟨8,by decide⟩) _ ready.slot8
  have r9 := row 9 (v ⟨9,by decide⟩) _ ready.slot9
  have r10 := row 10 (v ⟨10,by decide⟩) _ ready.slot10
  have r11 := row 11 (v ⟨11,by decide⟩) _ ready.lenSlot
  have r12 := row 12 (v ⟨12,by decide⟩) _ ready.exprSlot
  have r13 := row 13 (v ⟨13,by decide⟩) _ ready.slot13
  have r15 := row 15 (v ⟨15,by decide⟩) _ ready.slot15
  have r16 := row 16 (v ⟨16,by decide⟩) _ ready.slot16
  have slotPresent := GenericFunctionEntryNumerics.slot_lookup s.options s.remaining s.span raw s.tracker s.fresh s.id s.entry s.parentTag
    s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot slotAllocation
  have exprUnheld := GenericFunctionEntryNumerics.expression_unheld s.tracker s.fresh s.slotFresh s.exprUnheldInitial
  have baseEq : (config s.options s.remaining s.span).access.runtime.base = (config s.options (s.remaining+1) s.span).access.runtime.base := by
    rw [actual_access_runtime s.options () s.remaining s.span,actual_access_runtime s.options () (s.remaining+1) s.span]
  let input : GenericSharedRejectedInput.Base := {
    options := s.options
    limits := s.limits
    remaining := s.remaining
    budget := s.budget
    dispatchFuel := s.dispatchFuel
    span := s.span
    precise := s.precise
    implicitWrites := s.implicitWrites
    debug := s.debugOff
    cmp := s.cmp
    dynamicFuel := s.dynamicFuel
    validityFuel := s.validityFuel
    dynamicEq := s.fuelEq
    validationEq := s.validationEq
    id := s.id
    entry := entry
    base := s.base
    offset := s.offset
    len := s.len
    positive := s.positive
    nonnull := s.nonzero
    signedFits := s.signedFits
    frame := frame
    machine := machine
    tracker := tracker
    enabled := enabled
    defaultMode := s.mode
    fresh := s.exprFresh
    target := GeneralBorrowFreshMutableStages.slot_index s.data.slot
    first := first
    capacity := metadata.capacity.trans s.capacity
    owned := owned
    fresh2 := s.helperFresh
    tagFresh := (freshTags ⟨1,by decide⟩).1
    protectorFresh := (freshTags ⟨1,by decide⟩).2
    different := ne tracker.global.nextPointerTag tag1.global.nextPointerTag (by omega)
    v1 := v ⟨1,by decide⟩
    v11 := v ⟨11,by decide⟩
    v12 := v ⟨12,by decide⟩
    sourceLive := by simpa only [firstTag,baseEq] using congrArg (fun row => row.value) r1
    sourceCached := congrArg (fun row => row.layout) r1
    lenLive := congrArg (fun row => row.value) r11
    lenUncached := congrArg (fun row => row.layout) r11
    exprLive := congrArg (fun row => row.value) r12
    exprUncached := congrArg (fun row => row.layout) r12
    body := ready.body
    identity := ready.identity
    callee := ready.callee
    location := ready.location
    frameRace := ready.noClocks
    race := runtime.race
    ghost := runtime.ghost
    shallow := runtime.shallow
    cached := by rw [runtime.addresses];exact s.cachedAddress
    present := present
    metadata := by rw [runtime.types];exact s.metadata
    notConstructed := by rw [runtime.types];exact s.notConstructed
    backend := runtime.backend
    thread := thread
    active := threadActive
    threadCache := threadCache
    unchecked := runtime.unchecked
    noGc := runtime.noGc
    fixed := runtime.fixed
    source := s.source
    rangePositive := GenericFunctionEntryNumerics.range_positive s.offset s.len s.entry.allocation.byteSize.bytes s.positive s.bounds
    exprUnheld := exprUnheld
    size := ready.size
    count := s.count
    countPositive := s.countPositive
    rejected := s.rejected
    all := ready.immediate
    live0 := congrArg (fun row => row.value) r0
    cache0 := congrArg (fun row => row.layout) r0
    live7 := congrArg (fun row => row.value) r7
    live8 := congrArg (fun row => row.value) r8
    cache8 := congrArg (fun row => row.layout) r8
    live9 := congrArg (fun row => row.value) r9
    cache9 := congrArg (fun row => row.layout) r9
    live10 := congrArg (fun row => row.value) r10
    cache10 := congrArg (fun row => row.layout) r10
    live13 := congrArg (fun row => row.value) r13
    cache13 := congrArg (fun row => row.layout) r13
    initialActive := activeWithin
    targetNotExposed := firstNotExposed
    continuation := full.entry.continuation
    varargs := full.entry.varargs
    context := s.writeContext
    validationContext := s.validationContext
    accessEq := s.accessEq
    validationWidth := s.validationWidth
    validationRuntimeSize := s.validationRuntimeSize
    sameRuntime := s.sameRuntime
    width := s.width
    runtimeWidth := s.runtimeWidth
    runtimeSize := s.runtimeSize
    outerAccessEq := s.outerAccessEq
    slotId := s.slotId
    separate := s.separate
    slot := {s.slotEntry with allocation := slotAllocation}
    slotPresent := slotPresent
    slotRoot := s.slotRoot
    slotChild := (next s.tracker s.fresh).global.nextPointerTag
    slotTree := slotTree
    slotRootFree := buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct s.slotFree
    slotChildHeld := GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh
    slotDistinct := s.slotDistinct
    frameTracked := by simpa only [firstTag] using ready.borrowed
    slotSize := slotSize
    slotStorage := slotStorage
    slotMask := slotMask
    slotProvenance := slotProvenance
    slotMutable := slotMutable
    place := s.place
    layout := s.layout
    slotBase := s.slotBase
    slotPointer := s.slotPointer
    aligned := s.aligned
    fits := s.slotFits
    slotCached := by rw [runtime.addresses];exact s.slotCached
    extras := by rw [runtime.extras];exact s.extras
    destination := by rw [full.entry.returnPlace];rfl
    slotRootDifferent2 := s.slotRootHelper
    slotChildDifferent2 := childDifferent ⟨1,by decide⟩

  }
  refine ⟨input,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_,call,trace,rfl⟩

/-- Legacy allocator wrapper around the common genuine-entry builder. -/
theorem prepare {reuse : Bool} (s : Initial reuse) :
    ∃ input : GenericSharedRejectedInput.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      input.id=s.id ∧ input.count=s.count ∧ input.place=s.place ∧
      ∃ installed,
        Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
            (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
            ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
          ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
        SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
          (Storage.withCurrent #[] input.frame input.machine) ∧ installed.stack.frames.size=1 := by
  classical
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  have nonzero := UInt64.pos_iff_ne_zero.mp s.positive
  have room : s.entry.allocation.extra.tagMapping.mapping.size+2 ≤ 4294967295 := by have h:=s.roomShared;omega
  have initialAllocator := GenericFunctionEntryAllocatorChoice.of_premise (reuse := reuse) (tree := s.entry.allocation.extra) s.noFree
  have allocator := GenericFunctionEntryAllocatorChoice.allocator s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds initialAllocator
  have oldDifferent : s.tracker.global.nextPointerTag ≠ (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag := by
    have growth0 := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have growth1 := GenericFunctionEntryNumerics.successor_value (next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    change (next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at growth0
    change (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag.value.toNat = (next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at growth1
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  let first := GenericFunctionEntryAllocatorChoice.first s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds initialAllocator room
    (s.futureClean ⟨0,by decide⟩) (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag (s.futureMap ⟨0,by decide⟩) (s.futureNodes ⟨0,by decide⟩) oldDifferent
  have firstTag : first.parentTag = s.tracker.global.nextPointerTag := GenericFunctionEntryAllocatorChoice.tag
    s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds initialAllocator room
    (s.futureClean ⟨0,by decide⟩) (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag (s.futureMap ⟨0,by decide⟩) (s.futureNodes ⟨0,by decide⟩) oldDifferent
  have firstNotExposed : first.parentNode.isExposed = false := GenericFunctionEntryAllocatorChoice.not_exposed
    s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds initialAllocator room
    (s.futureClean ⟨0,by decide⟩) (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag (s.futureMap ⟨0,by decide⟩) (s.futureNodes ⟨0,by decide⟩) oldDifferent
  obtain ⟨common,options,limits,remaining,span,id,count,place,treeEq,installed,call,trace,depth⟩ := prepare_base s.toInitialBase first firstTag firstNotExposed
  have cleanAt (index : Fin 2) : GeneralBorrowFreshFutureClean.Clean common.entry.allocation.extra
      ⟨UInt32.ofNat (common.entry.allocation.extra.tagMapping.mapping.size+index.val)⟩ := by
    rw [treeEq]
    have later := (GenericFunctionEntryAllocatorChoice.later_clean s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds initialAllocator
      (index.val+1) (by omega) (by have h:=s.roomShared;have h2:=index.isLt;omega) (s.futureClean index)).2
    simpa only [allocator.2.2.2,Nat.add_assoc,Nat.add_comm 1 index.val] using later
  let input : GenericSharedRejectedInput.Input := {
    toBase := common
    noFree := by rw [treeEq];exact allocator.1
    room := by rw [treeEq,allocator.2.2.2];have h:=s.roomShared;omega
    cleanFuture := cleanAt ⟨1,by decide⟩ }
  exact ⟨input,options,limits,remaining,span,id,count,place,installed,call,trace,depth⟩

end DuplicatePrefix.GenericFunctionEntryRejected
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GenericFunctionEntryRejected." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved rejected function entry dependency {dependency}"
