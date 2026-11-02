import duplicate_prefix.GeneralBorrowForestEntryReleaseData
import duplicate_prefix.GeneralBorrowForestFunctionEntryInvocation
import duplicate_prefix.GenericFunctionEntryRuntime
import duplicate_prefix.GenericFunctionEntryNumerics
import duplicate_prefix.GeneralBorrowForestRootZeroPhysical
import duplicate_prefix.PositiveRootInstalledFrame
namespace DuplicatePrefix.GeneralBorrowForestFunctionEntryZero
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
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
  data : GeneralBorrowForestEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len
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
      location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none) entry.allocation.extra.locations
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

private theorem untick (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (facts : GenericSharedLenAccepted.RuntimeFacts options remaining span before (RootZeroCompleteState.tick options remaining span machine)) :
    GenericSharedLenAccepted.RuntimeFacts options remaining span before machine := by
  have data : (RootZeroCompleteState.tick options remaining span machine).user.addresses=machine.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  exact ⟨(RootZeroCompleteState.tick_ghost options remaining span machine).symm.trans facts.ghost,
    (RootZeroCompleteState.tick_shallow options remaining span machine).symm.trans facts.shallow,
    facts.race,data.1.symm.trans facts.addresses,data.2.1.symm.trans facts.types,data.2.2.1.symm.trans facts.extras,
    data.2.2.2.symm.trans facts.backend,
    (RootZeroCompleteState.tick_flags options remaining span machine).1.symm.trans facts.unchecked,
    (RootZeroCompleteState.tick_flags options remaining span machine).2.symm.trans facts.noGc,facts.fixed,facts.active⟩

/-- Form the zero-count physical-return contract from the original caller state
and a genuine root call. Positive slice length and all caller/configuration,
multiple-root graph/mutable/foreign/cache/activity/allocator/return-storage
hypotheses are explicit in Initial.
No intermediate operation, release plan or successful invocation is an input. -/
theorem prepare (s : Initial) :
    ∃ input : GeneralBorrowForestRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowForestFunctionEntryInvocation.enters s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel
      s.fuelEq s.validationEq s.id s.parentTag s.tracker s.base s.offset s.len 0 s.nonzero s.entry s.positive s.signedFits s.bounds
      s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh s.data s.capacity s.race s.metadata s.notConstructed
      s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize
      s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance
      s.noBackend s.extras s.thread s.active s.noCache
  let raw := RawRootInvocation.root s.before s.place s.race
  let rawMachine := RawRootInvocation.machine #[] s.before
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  let tag := (next s.tracker s.fresh).global.nextPointerTag
  let tracker := held s.tracker s.fresh s.slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  let machine := enteredMachine rawMachine s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
  have runtime := untick s.options s.remaining s.span s.before machine
    (GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed)
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have fsize := PositiveRootInstalledFrame.size raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  have nonzero := UInt64.pos_iff_ne_zero.mp s.positive
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  have rangePositive := GenericFunctionEntryNumerics.range_positive s.offset s.len s.entry.allocation.byteSize.bytes s.positive s.bounds
  obtain ⟨bufferData,anchorEq,lowerEq,upperEq⟩ := GeneralBorrowForestEntryReleaseData.prepare s.entry.allocation.extra s.tracker s.parentTag
    s.offset s.len nonzero s.data bounds s.clean s.fresh s.slotFresh s.successorFresh s.successorDifferent rangePositive
  let tree := GeneralBorrowForestArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra tree}
  let slot : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.slotEntry with allocation:=updated}
  let release : GeneralBorrowForestPhysicalReturnPlan.Input machine.memory tracker.global.protectedTags := {
    id := s.id,tag := s.tracker.global.nextPointerTag,buffer := buffer
    present := GenericFunctionEntryState.buffer_lookup rawMachine s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated (Ne.symm s.separate)
    anchor := bufferData.anchor,primary := bufferData.primary,extras := bufferData.extras
    lower := bufferData.lower,upper := bufferData.upper
    positive := bufferData.positive,fits := bufferData.fits,context := bufferData.context
    tagPresent := bufferData.tagPresent
    active := GeneralBorrowFreshActiveWithin.active_on tree bufferData.anchor .Write bufferData.lower bufferData.upper bufferData.well bufferData.within
    owned := bufferData.owned
    slotId := s.slotId,separate := s.separate,slot := slot
    slotPresent := GenericFunctionEntryNumerics.slot_lookup s.options s.remaining s.span rawMachine s.tracker s.fresh s.id s.entry
      s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
    slotRoot := s.slotRoot,slotChild := tag,slotTree := slotTree
    slotRootFree := GenericFunctionEntryState.buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct s.slotFree
    slotChildHeld := GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh
    slotDistinct := s.slotDistinct }
  obtain ⟨thread,active,top⟩ := runtime.active
  let input : GeneralBorrowForestRootZeroPhysical.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,source:=s.source,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=frame,size:=fsize,location:=floc,slot0:=by simpa using slots ⟨0,by decide⟩,
    slot3:=by simpa using slots ⟨3,by decide⟩,slot4:=by simpa using slots ⟨4,by decide⟩,slot5:=by simpa using slots ⟨5,by decide⟩,
    slot2:=by simpa using slots ⟨2,by decide⟩,
    immediate:=PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals s.before s.place s.race) adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag,
    body:=fb.trans raw.body,identity:=fi.trans raw.identity,callee:=fc.trans raw.callee,noLocalClocks:=frace.trans raw.noClocks,
    continuation:=frc.trans (RawRootInvocation.control s.before s.place s.race).2.2.1,varargs:=by rw [fva];rfl,
    machine:=machine,tracker:=tracker,tracked:=rfl,defaultMode:=s.mode,noClocks:=runtime.race,noBackend:=runtime.backend,
    ghost:=runtime.ghost,shallow:=runtime.shallow,unchecked:=runtime.unchecked,noGc:=runtime.noGc,fixed:=runtime.fixed,
    thread:=thread,active:=active,release:=release,frameTracked:=fborrow,
    slotSize:=slotSize,slotStorage:=slotLen,slotMask:=slotMask,slotProvenance:=slotProv,slotMutable:=slotMut,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [runtime.addresses];exact s.slotCached,
    extras:=by change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [runtime.extras];exact s.extras,
    destination:=by rw [frp];rfl }
  exact ⟨input,rfl,rfl,rfl,rfl,call⟩

theorem invoke (s : Initial) :
    ∃ input : GeneralBorrowForestRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) ∧ GeneralBorrowForestRootZeroPhysical.Result input := by
  obtain ⟨input,options,limits,remaining,span,call⟩ := prepare s
  exact ⟨input,options,limits,remaining,span,call,GeneralBorrowForestRootZeroPhysical.complete input⟩

end
end DuplicatePrefix.GeneralBorrowForestFunctionEntryZero
