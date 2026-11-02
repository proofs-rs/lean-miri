import duplicate_prefix.GeneralBorrowForestMixedLenCallReturnResources
import duplicate_prefix.GeneralBorrowForestRootRejectedPhysical
namespace DuplicatePrefix.GeneralBorrowForestRejectedAfterLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
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
  budget : Nat
  dispatchFuel : limits.callDispatch = budget+1
  span : PreparedContracts.FixedSpanQuery
  ctx : ActualReferenceContext.Context options remaining span
  debugOff : options.place.debugAssertions = false
  cmp : ProjectionMetadataFacts.NullComparator
  dynamicFuel : Nat
  validityFuel : Nat
  fuelEq : options.place.dynamicFuel = dynamicFuel+1
  validationEq : options.limits.validation = validityFuel+1
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  len : UInt64
  exprTag : BorTag
  positive : (0 : UInt64) < len
  nonzero : base+offset ≠ 0
  signedFits : len.toNat < 9223372036854775808
  bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat
  caller : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracker : MachineHooks.BorrowState
  enabled : machine.borrowTracker = some tracker
  defaultMode : tracker.retagMode = .Default
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  parent : UniIndex
  primary : UniIndex
  extras : List UniIndex
  context : GeneralBorrowForestAccessData.Context entry.allocation.extra parent primary extras
  covered : GeneralBorrowGraph.RootsCover entry.allocation.extra
  tagPresent : entry.allocation.extra.indexOfTag exprTag = some parent
  tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag
  nodeTags : ∀ index node, entry.allocation.extra.nodeAt index = some node → entry.allocation.extra.indexOfTag node.tag = some index
  unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none
  slot : GeneralBorrowFreshReborrowStages.Slot entry.allocation.extra context.depth parent
  fits : entry.allocation.extra.nodes.data.size ≤ 4294967296
  well : entry.allocation.extra.locations.WellFormed
  clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) entry.allocation.extra.locations
  rangePositive : offset.toNat < (offset+len).toNat
  owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data entry.allocation.extra location tracker.global.protectedTags parent primary extras (GeneralBorrowFreshMixedChild.extend (fun _ => true) parent.toNat)))
      offset (offset+len) entry.allocation.extra.locations
  allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize
  valid : 11 < caller.locals.size
  live : caller.locals[11].value = .live (.immediate .uninit)
  uncached : caller.locals[11].layout = none
  noClocks : caller.extra.dataRace = none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  race : machine.dataRace = none
  thread : Miri.Concurrency.ThreadRecord
  index : Nat
  current : CompilerFrameContext.ActualFrame
  active : machine.threads.activeThread? = some thread
  top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index
  presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current
  metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime
  notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false
  sourceBody : caller.body = RootBody.reflected.body.body
  identity : caller.bodyIdentity = RootBody.reflected.body.identity
  callee : caller.functionInstance = RootBody.reflected.functionInstance
  located : caller.location = .mir ⟨2,12⟩
  source : PreparedContracts.SourceComparator
  sourceValid : 12 < caller.locals.size
  sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm)
  sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout
  backend : machine.user.payload.payload.user.backend = .none
  beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0
  fixed : beforeMachine.threads.fixedScheduling = true
  target : UniIndex
  targetNode : TreeNode
  targetPresent : entry.allocation.extra.nodeAt target = some targetNode
  exprFree : tracker.global.protectedTags.contains context.anchorNode.tag = false
  prefixPath : ∀ location, (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath parent.toNat =
      parent.toNat :: (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat
  exprOutside : ∀ location, parent.toNat ∉ (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat
  rootPath : ∀ location, ((source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat
  targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)
  inputCount : UInt64
  rejected : inputCount > len/2
  frameSize : caller.locals.size = 25
  allImmediate : CopyHelperCleanup.AllImmediate caller
  live0 : (caller.locals[0]'(by omega)).value = .live (.immediate .uninit)
  cache0 : (caller.locals[0]'(by omega)).layout = none
  live7 : (caller.locals[7]'(by omega)).value = .live (.immediate .uninit)
  live8 : (caller.locals[8]'(by omega)).value = .live (.immediate .uninit)
  cache8 : (caller.locals[8]'(by omega)).layout = none
  live9 : (caller.locals[9]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 inputCount))))
  cache9 : (caller.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout
  live10 : (caller.locals[10]'(by omega)).value = .live (.immediate .uninit)
  cache10 : (caller.locals[10]'(by omega)).layout = none
  live13 : (caller.locals[13]'(by omega)).value = .live (.immediate .uninit)
  cache13 : (caller.locals[13]'(by omega)).layout = none
  continuation : caller.returnContinuation = .stop true
  varargs : caller.vaList = #[]
  slotId : AllocId
  slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotRoot : BorTag
  slotChild : BorTag
  slotBase : UInt64
  separate : slotId ≠ id
  slotPresent : beforeMachine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry)
  slotTree : slotEntry.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true
  slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1
  slotStorage : slotEntry.allocation.len = 1
  slotMask : slotEntry.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slotEntry.allocation.mutability = .Mut
  slotRootFree : ((TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall
    (({} : FrameState).addProtector id tracker.global.nextPointerTag)).protectedTags.contains slotRoot = false
  slotChildHeld : ((TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall
    (({} : FrameState).addProtector id tracker.global.nextPointerTag)).protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  frameTracked : caller.extra.borrowTracker = some ((({} : FrameState).addProtector id targetNode.tag).addProtector slotId slotChild)
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  slotFits : slotBase.toNat+1 < 2^64
  slotCached : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  slotExtras : beforeMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : caller.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
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

theorem prepare (s : Initial) :
    ∃ input : GeneralBorrowForestRootRejectedPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.beforeMachine) (Storage.withCurrent #[] input.before input.machine) := by
  obtain ⟨root,post,released,trace,rootEq,memoryEq,tracked,releaseEq,owned,runtime,context,tagPresent,fits,active⟩ :=
    GeneralBorrowForestMixedLenCallReturnResources.executes s.options s.limits s.remaining s.budget s.dispatchFuel s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.entry s.base s.offset s.len s.exprTag s.positive s.nonzero s.signedFits s.bounds #[] s.caller s.machine s.tracker s.enabled s.defaultMode s.fresh s.parent s.primary s.extras s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits s.well s.clean s.rangePositive s.owned s.allocationSize s.valid s.live s.uncached s.noClocks s.ghost s.shallow s.cachedAddress s.present s.race s.thread s.index s.current s.active s.top s.presentFrame s.metadata s.notConstructed s.sourceBody s.identity s.callee s.located s.source s.sourceValid s.sourceLive s.sourceCached s.backend s.beforeMachine s.machineEq s.unchecked s.noGc s.fixed s.target s.targetNode s.targetPresent s.exprFree s.prefixPath s.exprOutside s.rootPath s.targetActive
  obtain ⟨forestContext⟩ := context
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag
  let ended := {held with global := held.global.endCall (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag)}
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation := s.entry.allocation.setExtra released}
  have found : post.memory.live.find? (fun row => row.1 == s.id) = some (s.id,buffer) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same s.beforeMachine.memory s.id s.entry released
  have slotFound : post.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,s.slotEntry) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_other s.beforeMachine.memory s.id s.slotId s.entry s.slotEntry released s.separate s.slotPresent
  let release : GeneralBorrowForestPhysicalReturnPlan.Input post.memory ended.global.protectedTags := {
    id := s.id,tag := s.targetNode.tag,buffer := buffer,present := found,
    anchor := s.target,primary := s.primary,extras := s.extras,lower := s.offset,upper := s.offset+s.len,
    positive := s.rangePositive,fits := fits,context := forestContext,tagPresent := tagPresent,active := active,owned := owned,
    slotId := s.slotId,separate := s.separate,slot := s.slotEntry,slotPresent := slotFound,
    slotRoot := s.slotRoot,slotChild := s.slotChild,slotTree := s.slotTree,slotRootFree := s.slotRootFree,
    slotChildHeld := s.slotChildHeld,slotDistinct := s.slotDistinct }
  have rootSize : root.locals.size=25 := by rw [rootEq];simp [cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,s.frameSize]
  have keep (i : Nat) (valid : i<root.locals.size) (original : i<s.caller.locals.size) (different : i≠11) :
      root.locals[i]'valid = s.caller.locals[i]'original := by
    simp [rootEq,cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,Array.getElem_set,different,Ne.symm different]
  have slot11 : root.locals[11]'(by omega) =
      (⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.len)))),some RootCompilerFacts.usizeLayout⟩ : LocalState Provenance LocalLayout) := by
    simp [rootEq,cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame]
  obtain ⟨thread,threadActive⟩ := runtime.active
  let input : GeneralBorrowForestRootRejectedPhysical.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,source:=s.source,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=root,len:=s.len,count:=s.inputCount,rejected:=s.rejected,frameSize:=rootSize,location:=by rw [rootEq],
    all:=by
      rw [rootEq]
      change CopyHelperCleanup.AllImmediate (writeFrame (cachedCaller s.caller s.valid) 11 _ _)
      exact CopyHelperCleanup.all_immediate_set _ 11 _ _
        (CopyHelperCleanup.all_immediate_cache s.caller 11 RootCompilerFacts.usizeLayout _ s.allImmediate) (by intro memory;simp),
    temp12:=(RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.exprTag) (Size.ofBytes (s.base+s.offset))) s.len SharedReferenceMetadata.sharedLayout).imm,
    live12:=by rw [keep 12 (by omega) s.sourceValid (by decide)];exact s.sourceLive,
    live13:=by rw [keep 13 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live13,
    cache13:=by rw [keep 13 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache13,
    live0:=by rw [keep 0 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live0,
    cache0:=by rw [keep 0 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache0,
    live7:=by rw [keep 7 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live7,
    live8:=by rw [keep 8 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live8,
    cache8:=by rw [keep 8 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache8,
    live9:=by rw [keep 9 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live9,
    cache9:=by rw [keep 9 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache9,
    live10:=by rw [keep 10 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live10,
    cache10:=by rw [keep 10 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache10,
    live11:=congrArg LocalState.value slot11,cache11:=congrArg LocalState.layout slot11,
    body:=by rw [rootEq];exact s.sourceBody,identity:=by rw [rootEq];exact s.identity,callee:=by rw [rootEq];exact s.callee,
    noLocalClocks:=by rw [rootEq];exact s.noClocks,continuation:=by rw [rootEq];exact s.continuation,varargs:=by rw [rootEq];exact s.varargs,
    machine:=post,tracker:=ended,tracked:=tracked,defaultMode:=s.defaultMode,noClocks:=runtime.race,noBackend:=runtime.backend,
    ghost:=runtime.ghost,shallow:=runtime.shallow,unchecked:=runtime.unchecked,noGc:=runtime.noGc,fixed:=runtime.fixed,
    thread:=thread,active:=threadActive,release:=release,frameTracked:=by rw [rootEq];exact s.frameTracked,
    slotSize:=s.slotSize,slotStorage:=s.slotStorage,slotMask:=s.slotMask,slotProvenance:=s.slotProvenance,slotMutable:=s.slotMutable,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [runtime.addresses];exact s.slotCached,
    extras:=by change post.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [runtime.extras];exact s.slotExtras,
    destination:=by rw [rootEq];exact s.destination }
  exact ⟨input,rfl,rfl,rfl,rfl,trace⟩

theorem complete (s : Initial) :
    ∃ input : GeneralBorrowForestRootRejectedPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.beforeMachine) (Storage.withCurrent #[] input.before input.machine) ∧
      GeneralBorrowForestRootRejectedPhysical.Result input := by
  obtain ⟨input,a,b,c,d,prefixTrace⟩ := prepare s
  exact ⟨input,a,b,c,d,prefixTrace,GeneralBorrowForestRootRejectedPhysical.complete input⟩
end
end DuplicatePrefix.GeneralBorrowForestRejectedAfterLen
