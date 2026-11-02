import duplicate_prefix.GeneralBorrowForestAsMutDefaultReturn
import duplicate_prefix.GenericLenAcceptedPrelude
namespace DuplicatePrefix.GeneralBorrowForestAcceptedAfterLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- Raw initial records at the real len-helper return PC3:0. Every future
mutable expression, FnEntry, release and physical return is derived internally.
No successful operation or post-guard input is a field. -/
structure Initial where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  debug : options.place.debugAssertions = false
  fuel : Nat
  validation : options.limits.validation = fuel+1
  dynamicFuel : Nat
  dynamic : options.place.dynamicFuel = dynamicFuel+1
  cmp : ProjectionMetadataFacts.NullComparator
  source : PreparedContracts.SourceComparator
  budget : Nat
  dispatch : limits.callDispatch = budget+1
  caller : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  len : UInt64
  positive : (0 : UInt64) < len
  nonzero : base+offset ≠ 0
  signedFits : len.toNat < 9223372036854775808
  bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat
  cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  parentTag : BorTag
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  mode : tracker.retagMode = .Default
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  race : machine.dataRace = none
  backend : machine.user.payload.payload.user.backend = .none
  clocks : caller.extra.dataRace = none
  metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime
  notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).entries.any (·.value.ty == 4) = false
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread
  top : thread.topUserRelevantFrame = some 0
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  size : caller.locals.size = 25
  body : caller.body = RootBody.reflected.body.body
  identity : caller.bodyIdentity = RootBody.reflected.body.identity
  callee : caller.functionInstance = RootBody.reflected.functionInstance
  track : caller.trackCallerArg = none
  relevant : caller.extra.userRelevance > 0
  immediate : CopyHelperCleanup.AllImmediate caller
  count : UInt64
  countPositive : (0 : UInt64) < count
  within : count ≤ len/2
  slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩
  capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize
  runtimeContext : ActualReferenceContext.Context options remaining span
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  data : GeneralBorrowForestEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len
  storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFits : entry.allocation.len+64 < 18446744073709551616
  mutable : entry.allocation.mutability = .Mut
  bufferExtras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  zero : caller.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  continuation : caller.returnContinuation = .stop true
  varargs : caller.vaList = #[]
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
  slotRootNotHelper : tracker.global.nextPointerTag ≠ slotRoot
  slotRootFree : tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  slotChildNotHelper : slotChild ≠ tracker.global.nextPointerTag
  frameTracked : caller.extra.borrowTracker = some
    ((({} : FrameState).addProtector id parentTag).addProtector slotId slotChild)
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
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : caller.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
  statementFuel : limits.validation = fuel+1
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  location : caller.location = .mir ⟨3,0⟩
  valid1 : (1 : MIR.LocalId) < caller.locals.size
  value1 : caller.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)
  cached1 : caller.locals[1].layout = some ActualReferenceMetadata.reference
  temp12 : Immediate Provenance
  live12 : (caller.locals[12]'(by omega)).value = .live (.immediate temp12)
  live13 : (caller.locals[13]'(by omega)).value = .live (.immediate .uninit)
  cache13 : (caller.locals[13]'(by omega)).layout = none
  live0 : (caller.locals[0]'(by omega)).value = .live (.immediate .uninit)
  cache0 : (caller.locals[0]'(by omega)).layout = none
  live7 : (caller.locals[7]'(by omega)).value = .live (.immediate .uninit)
  cache7 : (caller.locals[7]'(by omega)).layout = none
  dead15 : (caller.locals[15]'(by omega)).value = .dead
  cache15 : (caller.locals[15]'(by omega)).layout = none
  dead16 : (caller.locals[16]'(by omega)).value = .dead
  cache16 : (caller.locals[16]'(by omega)).layout = none
  live8 : (caller.locals[8]'(by omega)).value = .live (.immediate .uninit)
  cache8 : (caller.locals[8]'(by omega)).layout = none
  live9 : (caller.locals[9]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count))))
  cache9 : (caller.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout
  live10 : (caller.locals[10]'(by omega)).value = .live (.immediate .uninit)
  cache10 : (caller.locals[10]'(by omega)).layout = none
  live11 : (caller.locals[11]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len))))
  cache11 : (caller.locals[11]'(by omega)).layout = some RootCompilerFacts.usizeLayout
  targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra data.parent .Write offset (offset+len)
  rootPath : ∀ location, ((source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath data.parent.toNat).getLast! = data.primary.toNat
  targetNotHelper : tracker.global.nextPointerTag ≠ parentTag
  allocator : GeneralBorrowGcAllocator.Invariant entry.allocation.extra
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  room : entry.allocation.extra.nodes.size+5 ≤ 4294967295
  freshNext : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615
  mapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
    (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  unheld : tracker.global.protectedTags.get (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag = none
  expressionUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false
  targetDifferent : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠ parentTag
  rootDifferent : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠ slotRoot
  childDifferent : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag

def machine (s : Initial) := RootZeroCompleteState.tick s.options s.remaining s.span
  (RootZeroCompleteState.tick s.options s.remaining s.span s.machine)

structure MachineFields (s : Initial) : Prop where
  memory : (machine s).memory = s.machine.memory
  tracked : (machine s).borrowTracker = s.machine.borrowTracker
  race : (machine s).dataRace = s.machine.dataRace
  threads : (machine s).threads = s.machine.threads
  addresses : (machine s).user.addresses = s.machine.user.addresses
  types : (machine s).user.payload.payload.user.types = s.machine.user.payload.payload.user.types
  extras : (machine s).user.payload.payload.user.runtime.extras = s.machine.user.payload.payload.user.runtime.extras
  backend : (machine s).user.payload.payload.user.backend = s.machine.user.payload.payload.user.backend

theorem machine_fields (s : Initial) : MachineFields s := by
  constructor <;> unfold machine RootZeroCompleteState.tick SourceControl.accounted <;> rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators] <;> rfl

/-- Execute the real accepted guard and assemble every suffix input from the
initial caller, allocation and resource records. -/
theorem prepare (s : Initial) :
    ∃ ready : GeneralBorrowForestAsMutDefaultToCall.Input,
      PreparedContracts.actualConfig ready.base.data.start.options () (ready.base.data.start.remaining+1) ready.base.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      ready.base.data.start.limits = s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.machine)
        (Storage.withCurrent #[] ready.base.caller ready.base.data.start.machine) := by
  obtain ⟨frame,properties,facts⟩ := GenericLenAcceptedPrelude.executes_full s.options s.limits s.remaining s.span s.source s.debug s.fuel s.validation
    s.caller s.machine s.len s.count s.countPositive s.within s.size s.temp12 s.live12 s.live13 s.cache13 s.live0 s.cache0
    s.live7 s.cache7 s.dead15 s.cache15 s.dead16 s.cache16 s.live8 s.cache8 s.live9 s.cache9 s.live10 s.cache10 s.live11 s.cache11
    s.body s.identity s.callee s.location s.immediate s.clocks s.tracker s.tracked s.mode s.ghost s.shallow s.unchecked s.noGc s.fixed
  rcases properties with ⟨trace,rbody,ridentity,rcallee,rextra,rreturn,rcont,rva,rlocal,rtrack,rsize,rlocation,r1,r2,r15,r16,rall⟩
  have fields := machine_fields s
  have valid15 : (15 : MIR.LocalId) < frame.locals.size := by rw [rsize];decide
  let cached := AsMutUncachedCall.cachedCaller frame valid15
  have cachedSize : cached.locals.size = frame.locals.size := by simp only [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  have same (index : MIR.LocalId) (different : index ≠ 15) : cached.locals[index]? = frame.locals[index]? := by
    simp only [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different,ite_false]
  have row15 : cached.locals[15]? = some ⟨.live (.immediate .uninit),some CopyCompilerFacts.destPointerLayout⟩ := by
    have old := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans r15)
    simp only [cached,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set_self,old]
  have valid15c : (15 : MIR.LocalId) < cached.locals.size := by rw [cachedSize];exact valid15
  have cell15 : (cached.locals[15]'valid15c) = ⟨.live (.immediate .uninit),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid15c).symm.trans row15)
  have immediate : CopyHelperCleanup.AllImmediate cached := by
    apply CopyHelperCleanup.all_immediate_set frame 15 {frame.locals[15] with layout := some CopyCompilerFacts.destPointerLayout} valid15 rall
    intro memory
    exact rall frame.locals[15] (Array.getElem_mem valid15) memory
  have ghost : (machine s).user.payload.ghost = false :=
    (RootZeroCompleteState.tick_ghost s.options s.remaining s.span _).trans
      ((RootZeroCompleteState.tick_ghost s.options s.remaining s.span s.machine).trans s.ghost)
  have shallow : (machine s).user.payload.validation = .Shallow :=
    (RootZeroCompleteState.tick_shallow s.options s.remaining s.span _).trans
      ((RootZeroCompleteState.tick_shallow s.options s.remaining s.span s.machine).trans s.shallow)
  have unchecked : ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl (machine s).user).checkedArithmetic = false :=
    (RootZeroCompleteState.tick_flags s.options s.remaining s.span _).1.trans
      ((RootZeroCompleteState.tick_flags s.options s.remaining s.span s.machine).1.trans s.unchecked)
  have noGc : ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl (machine s).user).gcInterval = 0 :=
    (RootZeroCompleteState.tick_flags s.options s.remaining s.span _).2.trans
      ((RootZeroCompleteState.tick_flags s.options s.remaining s.span s.machine).2.trans s.noGc)
  have clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get
      (GeneralBorrowFreshMutableStages.slot_index s.data.slot) = none) s.entry.allocation.extra.locations := by
    apply s.vacantClean
    exact GeneralBorrowFreshMutableStages.slot_vacant _ _ _ s.data.slot
  let core : GeneralBorrowForestAsMutInvocationCore.Input := by
    refine {
      options := s.options, limits := s.limits, remaining := s.remaining, span := s.span, debug := s.debug
      fuel := s.fuel, validation := s.validation, dynamicFuel := s.dynamicFuel, dynamic := s.dynamic
      cmp := s.cmp, source := s.source, budget := s.budget, dispatch := s.dispatch
      caller := cached, machine := machine s, id := s.id, entry := s.entry, base := s.base, offset := s.offset, len := s.len
      positive := s.positive, nonzero := s.nonzero, signedFits := s.signedFits, bounds := s.bounds, cachedAddress := ?_, present := ?_
      parentTag := s.parentTag, tracker := s.tracker, tracked := fields.tracked.trans s.tracked, mode := s.mode
      ghost := ghost, shallow := shallow, race := fields.race.trans s.race, backend := fields.backend.trans s.backend
      valid15 := valid15c, live15 := congrArg LocalState.value cell15, cached15 := congrArg LocalState.layout cell15
      clocks := rextra ▸ s.clocks, metadata := ?_, notConstructed := ?_, thread := s.thread, active := ?_, top := s.top
      unchecked := unchecked, noGc := noGc, fixed := ?_
      size := cachedSize.trans rsize, body := rbody.trans s.body, identity := ridentity.trans s.identity, callee := rcallee.trans s.callee
      track := rtrack.trans s.track, relevant := ?_, immediate := immediate, temp16 := .uninit
      live16 := ?_, count := s.count, countPositive := s.countPositive, within := s.within, slot2 := ?_, slot13 := ?_, unused := ?_
      capacity := s.capacity, runtimeContext := s.runtimeContext, fresh := s.fresh, data := s.data, clean := clean }
    · rw [fields.addresses];exact s.cachedAddress
    · rw [fields.memory];exact s.present
    · change (machine s).user.payload.payload.user.types.metadata = _
      rw [fields.types];exact s.metadata
    · change (machine s).user.payload.payload.user.types.entries.any _ = _
      rw [fields.types];exact s.notConstructed
    · rw [fields.threads];exact s.active
    · rw [fields.threads];exact s.fixed
    · change frame.extra.userRelevance > 0
      rw [rextra];exact s.relevant
    · rw [same 16 (by decide),r16];rfl
    · exact (same 2 (by decide)).trans (r2.trans s.slot2)
    · exact (same 13 (by decide)).trans facts.slot13
    · intro index lower upper
      have different : index ≠ 15 := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 15 < 17) lower))
      exact (same index different).trans ((facts.high index lower).trans (s.unused index lower upper))
  let physical : GeneralBorrowForestAsMutInvocation.Input := by
    refine {
      start := core, statementFuel := s.statementFuel, target := s.data.parent, targetNode := s.data.context.anchorNode, targetPresent := s.data.context.anchorPresent
      targetNotExposed := s.data.context.unexposed _ _ s.data.context.anchorPresent, targetTag := s.parentTag, targetNotHelper := s.targetNotHelper
      targetTagPresent := s.data.tagPresent, targetRootPath := s.rootPath, targetWithin := s.targetActive
      subset := by intro _ _ member;exact member
      escaping := by intro _ _ _ _ localMember foreignMember;exact False.elim (foreignMember localMember)
      storage := s.storage, maskValid := s.maskValid, maskLength := s.maskLength, initialized := s.initialized
      provenance := s.provenance, storageFits := s.storageFits, mutable := s.mutable, bufferExtras := ?_, bounded := s.bounded
      zero := (same 0 (by decide)).trans (facts.slot0.trans s.zero), continuation := rcont.trans s.continuation
      varargs := rva.trans s.varargs, context := s.context, validationContext := s.validationContext
      accessEq := s.accessEq, validationWidth := s.validationWidth, validationRuntimeSize := s.validationRuntimeSize
      sameRuntime := s.sameRuntime, width := s.width, runtimeWidth := s.runtimeWidth, runtimeSize := s.runtimeSize, outerAccessEq := s.outerAccessEq
      slotId := s.slotId, separate := s.separate, slot := s.slot, slotPresent := ?_, slotRoot := s.slotRoot, slotChild := s.slotChild
      slotTree := s.slotTree, slotRootNotHelper := s.slotRootNotHelper, slotRootFree := s.slotRootFree, slotChildHeld := s.slotChildHeld
      slotDistinct := s.slotDistinct, slotChildNotHelper := s.slotChildNotHelper, frameTracked := ?_
      slotSize := s.slotSize, slotStorage := s.slotStorage, slotMask := s.slotMask, slotProvenance := s.slotProvenance, slotMutable := s.slotMutable
      place := s.place, layout := s.layout, slotBase := s.slotBase, slotPointer := s.slotPointer, aligned := s.aligned, fits := s.fits
      cached := ?_, extras := ?_, destination := (congrArg (fun place => place.toRuntimePlace) rreturn).trans s.destination }
    · rw [fields.extras];exact s.bufferExtras
    · rw [fields.memory];exact s.slotPresent
    · change frame.extra.borrowTracker = _
      rw [rextra];exact s.frameTracked
    · rw [fields.addresses];exact s.cached
    · rw [fields.extras];exact s.extras
  have valid1 : (1 : MIR.LocalId) < frame.locals.size := by rw [rsize];decide
  have valid16 : (16 : MIR.LocalId) < frame.locals.size := by rw [rsize];decide
  have source1 : (frame.locals[1]'valid1) = (s.caller.locals[1]'s.valid1) :=
    Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (r1.trans (Array.getElem?_eq_getElem s.valid1)))
  have cell15raw : frame.locals[15] = ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans r15)
  have cell16raw : frame.locals[16] = ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans r16)
  let ready : GeneralBorrowForestAsMutDefaultToCall.Input := {
    base := {
      data := physical, caller := frame, valid15 := valid15, cached := rfl
      live15 := congrArg LocalState.value cell15raw, uncached15 := congrArg LocalState.layout cell15raw
      preciseOff := s.preciseOff, implicitOff := s.implicitOff, location := rlocation, valid1 := valid1
      value1 := by rw [source1];exact s.value1
      cached1 := by rw [source1];exact s.cached1
      valid16 := valid16, live16 := congrArg LocalState.value cell16raw, uncached16 := congrArg LocalState.layout cell16raw }
    target := rfl, fresh := s.freshNext, allocator := s.allocator, vacantClean := s.vacantClean, room := s.room
    mapFresh := s.mapFresh, different := s.different, unheld := s.unheld, expressionUnheld := s.expressionUnheld
    targetDifferent := s.targetDifferent, rootDifferent := s.rootDifferent, childDifferent := s.childDifferent }
  exact ⟨ready,rfl,rfl,trace⟩

/-- From the actual post-len ROOT PC3:0, the accepted positive-count branch
executes guards, mutable expression, FnEntry, as_mut_ptr, adjacent physical
copy, both root releases and a physical true return. All successful finite
Unit-choice prefixes are free of interpreter errors. -/
theorem invoke (s : Initial) :
    let cfg := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] s.caller s.machine
    ∃ ready : GeneralBorrowForestAsMutPhysicalReturn.Input, ∃ finalState,
      GeneralBorrowForestAsMutPhysicalReturn.Result ready ∧
      SuccessfulTrace.Trace cfg s.limits initial finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 initial ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits initial before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  obtain ⟨suffix,configEq,limitsEq,leadingTrace⟩ := prepare s
  obtain ⟨ready,finalState,physical,tail,terminal,empty,_,_⟩ := GeneralBorrowForestAsMutDefaultReturn.complete suffix
  rw [configEq,limitsEq] at tail terminal
  have full := SuccessfulTrace.append leadingTrace tail
  have safety := SuccessfulTrace.no_ub
    (⟨PreparedContracts.actualConfig s.options () (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 (Storage.withCurrent #[] s.caller s.machine) finalState ⟨by decide,rfl⟩ full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨ready,finalState,physical,full,terminal,empty,safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩

end
end DuplicatePrefix.GeneralBorrowForestAcceptedAfterLen
