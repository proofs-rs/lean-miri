import duplicate_prefix.GeneralBorrowForestAsMutEntryTree
import duplicate_prefix.GeneralBorrowForestAsMutEntryState
import duplicate_prefix.GeneralBorrowForestAsMutPhysicalReturn

namespace DuplicatePrefix.GeneralBorrowForestAsMutInvocationCore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Caller and memory data before the actual as_mut_ptr call. Mutable FnEntry
ownership and release contracts are derived, rather than supplied here. -/
structure Input where
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
  valid15 : (15 : MIR.LocalId) < caller.locals.size
  live15 : (caller.locals[15]'valid15).value = .live (.immediate .uninit)
  cached15 : (caller.locals[15]'valid15).layout = some CopyCompilerFacts.destPointerLayout
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
  temp16 : Immediate Provenance
  live16 : caller.locals[16]?.map (·.value) = some (.live (.immediate temp16))
  count : UInt64
  countPositive : (0 : UInt64) < count
  within : count ≤ len/2
  slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot13 : caller.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩
  capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize
  runtimeContext : ActualReferenceContext.Context options remaining span
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  data : GeneralBorrowForestEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len
  clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) entry.allocation.extra.locations

noncomputable def pushed (s : Input) :=
  (AsMutPush.completed s.options.userRelevantCrates (Storage.withCurrent #[] s.caller s.machine)
    (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView s.caller).machine

noncomputable def after (s : Input) :=
  GeneralBorrowForestAsMutEntryState.machine (pushed s) s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len

noncomputable def entry (s : Input) : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {s.entry with allocation := (s.entry.allocation.setExtra
    (GeneralBorrowForestArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len))}

noncomputable def parent (s : Input) :=
  (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig s.options () s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm

noncomputable def body_input (s : Input)
    (release : GeneralBorrowForestAsMutReleasePlan.Input (entry s).allocation.extra
      (GeneralBorrowForestAsMutEntryState.tracker s.tracker s.fresh).global.protectedTags s.tracker.global.nextPointerTag) :
    GeneralBorrowForestAsMutBodyToCopy.Input := by
  have push := GeneralBorrowForestAsMutEntryState.push_fields s.options.userRelevantCrates s.caller s.machine
    (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView s.thread s.active
  have mem : (pushed s).memory = s.machine.memory := push.1
  have race : (pushed s).dataRace = s.machine.dataRace := push.2.2.1
  have ghost : (pushed s).user.payload.ghost = s.machine.user.payload.ghost := push.2.2.2.1
  have shallow : (pushed s).user.payload.validation = s.machine.user.payload.validation := push.2.2.2.2.1
  have user : (pushed s).user.payload.payload.user = s.machine.user.payload.payload.user := push.2.2.2.2.2.1
  have addresses : (pushed s).user.addresses = s.machine.user.addresses := push.2.2.2.2.2.2.1
  have fixed : (pushed s).threads.fixedScheduling = s.machine.threads.fixedScheduling := push.2.2.2.2.2.2.2.1
  have active := push.2.2.2.2.2.2.2.2
  refine {
    options := s.options, limits := s.limits, remaining := s.remaining, span := s.span
    debug := s.debug, fuel := s.fuel, validation := s.validation, dynamicFuel := s.dynamicFuel, dynamic := s.dynamic
    cmp := s.cmp, source := s.source, budget := s.budget, dispatch := s.dispatch
    caller := s.caller, initial := Storage.withCurrent #[] s.caller s.machine, initialRace := s.race
    parent := parent s, machine := after s, id := s.id, tag := s.tracker.global.nextPointerTag
    entry := entry s, base := s.base, offset := s.offset, len := s.len
    positive := s.positive, nonzero := s.nonzero, signedFits := s.signedFits, bounds := s.bounds
    cachedAddress := ?_, present := ?_, tracker := GeneralBorrowForestAsMutEntryState.tracker s.tracker s.fresh
    tracked := rfl, mode := s.mode, release := release
    ghost := ghost.trans s.ghost, shallow := shallow.trans s.shallow, race := race.trans s.race, backend := ?_
    valid15 := s.valid15, live15 := s.live15, cached15 := s.cached15, clocks := s.clocks
    metadata := ?_, notConstructed := ?_, thread := s.thread, newRank := AsMutFrame.rank s.options.userRelevantCrates
    oldRank := s.caller.extra.userRelevance, active := active, top := s.top
    unchecked := ?_, noGc := ?_, fixed := fixed.trans s.fixed
    size := s.size, body := s.body, identity := s.identity, callee := s.callee, track := s.track
    relevant := s.relevant, immediate := s.immediate, temp16 := s.temp16, live16 := s.live16
    count := s.count, countPositive := s.countPositive, within := s.within, slot2 := s.slot2, slot13 := s.slot13, unused := s.unused }
  · change (pushed s).user.addresses.baseAddr.find? _ = _
    rw [addresses]
    exact s.cachedAddress
  · exact StackPopRelease.lookup_commit_same (pushed s).memory s.id s.entry _
  · change (pushed s).user.payload.payload.user.backend = _
    rw [user]
    exact s.backend
  · change (pushed s).user.payload.payload.user.types.metadata = _
    rw [user]
    exact s.metadata
  · change (pushed s).user.payload.payload.user.types.entries.any _ = _
    rw [user]
    exact s.notConstructed
  · change ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl (pushed s).user).checkedArithmetic = false
    have control : (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl (pushed s).user =
        (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl s.machine.user := by
      rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
      change (pushed s).user.payload.payload.user.host.control = s.machine.user.payload.payload.user.host.control
      rw [user]
    rw [control]
    exact s.unchecked
  · change ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl (pushed s).user).gcInterval = 0
    have control : (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl (pushed s).user =
        (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl s.machine.user := by
      rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
      change (pushed s).user.payload.payload.user.host.control = s.machine.user.payload.payload.user.host.control
      rw [user]
    rw [control]
    exact s.noGc

/-- Actual source call entry into the initialized-helper state used below. -/
theorem actual_entry (s : Input)
    (release : GeneralBorrowForestAsMutReleasePlan.Input (entry s).allocation.extra
      (GeneralBorrowForestAsMutEntryState.tracker s.tracker s.fresh).global.protectedTags s.tracker.global.nextPointerTag) :
    let body := body_input s release
    let destination := (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate (parent s),ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue)
      (Storage.withCurrent #[] s.caller s.machine) =
      .ok () (Storage.withCurrent #[s.caller] (GeneralBorrowForestAsMutBodyToCopy.helper body) (after s)) := by
  have top : FrameRelevance.top
      (AsMutPush.pushed s.options.userRelevantCrates (Storage.withCurrent #[] s.caller s.machine)
        (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView).stack s.thread.topUserRelevantFrame = some 0 := by
    rw [FrameRelevance.top,s.top]
    rfl
  have present :
      (AsMutPush.pushed s.options.userRelevantCrates (Storage.withCurrent #[] s.caller s.machine)
        (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[0]? = some s.caller := rfl
  exact GeneralBorrowForestAsMutEntry.actual_entry s.options s.limits s.remaining s.span s.runtimeContext s.debug s.cmp s.dynamicFuel s.fuel
    s.dynamic s.validation s.id s.entry s.base s.offset s.len s.parentTag s.positive s.nonzero s.signedFits s.bounds
    #[] s.caller s.machine s.tracker s.tracked s.mode s.fresh s.data s.capacity 15 s.valid15 .uninit s.live15 s.cached15
    s.clocks s.ghost s.shallow s.cachedAddress s.present s.race s.metadata s.notConstructed s.thread 0 s.caller s.active top present

end DuplicatePrefix.GeneralBorrowForestAsMutInvocationCore
