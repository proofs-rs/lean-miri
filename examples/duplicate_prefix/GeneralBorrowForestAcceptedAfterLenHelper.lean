import duplicate_prefix.GeneralBorrowForestMixedLenCallReturnResources
import duplicate_prefix.GeneralBorrowForestAcceptedAfterLen
import duplicate_prefix.GeneralBorrowForestAcceptedAfterLenRuntime
import duplicate_prefix.GeneralBorrowForestReleaseVacantClean
import duplicate_prefix.GeneralBorrowForestMixedSharedVacantClean
import duplicate_prefix.GeneralBorrowForestForeignSharedResources
import duplicate_prefix.GeneralBorrowCanonicalParentDepth
import duplicate_prefix.GeneralBorrowFreshMutablePathData
import duplicate_prefix.ProtectorRoundTrip
namespace DuplicatePrefix.GeneralBorrowForestAcceptedAfterLenHelper
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
  count : UInt64
  countPositive : (0 : UInt64) < count
  within : count ≤ len/2
  frameSize : caller.locals.size = 25
  allImmediate : CopyHelperCleanup.AllImmediate caller
  live0 : (caller.locals[0]'(by omega)).value = .live (.immediate .uninit)
  cache0 : (caller.locals[0]'(by omega)).layout = none
  live7 : (caller.locals[7]'(by omega)).value = .live (.immediate .uninit)
  live8 : (caller.locals[8]'(by omega)).value = .live (.immediate .uninit)
  cache8 : (caller.locals[8]'(by omega)).layout = none
  live9 : (caller.locals[9]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count))))
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

  statementFuel : limits.validation = validityFuel+1
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  cache7 : (caller.locals[7]'(by omega)).layout = none
  dead15 : (caller.locals[15]'(by omega)).value = .dead
  cache15 : (caller.locals[15]'(by omega)).layout = none
  dead16 : (caller.locals[16]'(by omega)).value = .dead
  cache16 : (caller.locals[16]'(by omega)).layout = none
  valid1 : (1 : MIR.LocalId) < caller.locals.size
  value1 : caller.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id targetNode.tag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)
  cached1 : caller.locals[1].layout = some ActualReferenceMetadata.reference
  slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩
  trackNone : caller.trackCallerArg = none
  relevant : caller.extra.userRelevance > 0
  rootMetadata : beforeMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  rootNotConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
  storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize
  initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageFits : entry.allocation.len+64 < 18446744073709551616
  mutable : entry.allocation.mutability = .Mut
  bufferExtras : beforeMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  allocator : GeneralBorrowGcAllocator.Invariant entry.allocation.extra
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  room : entry.allocation.extra.nodes.size+6 ≤ 4294967295
  fresh3 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615
  fresh4 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag.value < 18446744073709551615
  map3 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  map4 : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag
  unheld3 : tracker.global.protectedTags.get (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag = none
  unheld4 : tracker.global.protectedTags.get (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag = none
  different23 : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  different24 : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag
  different34 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag
  targetDifferent3 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠ targetNode.tag
  targetDifferent4 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag ≠ targetNode.tag
  slotRootDifferent3 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ≠ slotRoot
  slotRootDifferent4 : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag ≠ slotRoot
  slotChildDifferent3 : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  slotChildDifferent4 : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) fresh3).global.nextPointerTag

def held (s : Initial) := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag

def ended (s : Initial) := {held s with global := (held s).global.endCall (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag)}

def childTree (s : Initial) := GeneralBorrowForestMixedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len

def releasedTree (s : Initial) := ((childTree s).releaseProtector s.tracker.global.nextPointerTag (held s).global.protectedTags).tree

theorem ended_get (s : Initial) (tag : BorTag) (different : s.tracker.global.nextPointerTag ≠ tag) :
    (ended s).global.protectedTags.get tag = s.tracker.global.protectedTags.get tag := by
  simpa only [ended,held,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,
    ReferenceBorrowDriver.allocatedTracker] using
    ProtectorRoundTrip.singleton_get (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global s.id
      s.tracker.global.nextPointerTag tag .StrongProtector (Ne.symm different)

structure Resources (s : Initial) where
  data : GeneralBorrowForestEntryValidity.Data (releasedTree s) (ended s).global.protectedTags s.targetNode.tag
    (ended s).global.nextPointerTag s.offset s.len
  parent : data.parent = s.target
  primary : data.primary = s.primary
  extras : data.extras = s.extras
  allocator : GeneralBorrowGcAllocator.Invariant (releasedTree s)
  vacantClean : GeneralBorrowGcVacantClean.VacantClean (releasedTree s)
  capacity : (releasedTree s).locations.size = s.entry.allocation.extra.locations.size
  active : GeneralBorrowFreshActiveWithin.ActiveWithin (releasedTree s) s.target .Write s.offset (s.offset+s.len)
  rootPath : ∀ location, ((source_normal_projection (releasedTree s) location (ended s).global.protectedTags).topology.ancestorPath s.target.toNat).getLast! = s.primary.toNat
  room : (releasedTree s).nodes.size+5 ≤ 4294967295
  map4 : GeneralBorrowTagMap.Fresh (releasedTree s).tagMapping
    (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.fresh3).global.nextPointerTag

def resources (s : Initial) : Resources s := by
  let labels := GeneralBorrowFreshMixedChild.extend (fun _ => true) s.parent.toNat
  have nonzero : s.len ≠ 0 := UInt64.pos_iff_ne_zero.mp s.positive
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.allocationSize];exact s.bounds
  have registration := GeneralBorrowForestMixedRegister.registered s.entry.allocation.extra s.tracker.global {} s.id
    s.tracker.global.nextPointerTag .StrongProtector s.parent s.primary s.extras labels s.tagFresh s.nodeTags s.unheld s.offset (s.offset+s.len) s.owned
  let protections := (TypedBorrowSteps.registeredGlobal s.tracker s.tracker.global.nextPointerTag).protectedTags
  have foreign : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestForeignAccess.LocationData s.entry.allocation.extra location protections s.parent s.primary s.extras .Read))
      s.offset (s.offset+s.len) s.entry.allocation.extra.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩ := registration.2.2.2 position valid positive lower upper
    exact ⟨data.base⟩
  have allocated := GeneralBorrowForestForeignSharedResources.preserves s.entry.allocation.extra protections s.exprTag s.tracker.global.nextPointerTag true
    s.parent s.primary s.extras s.offset s.len .VisitChildrenOfAccessed s.context s.covered s.tagPresent s.tagFresh s.slot s.fits nonzero s.well bounds s.allocator foreign
  change GeneralBorrowGcAllocator.Invariant (childTree s) ∧ (childTree s).locations.WellFormed ∧
    (childTree s).locations.size = s.entry.allocation.extra.locations.size ∧ (childTree s).nodes.size ≤ s.entry.allocation.extra.nodes.size+1 ∧
    GeneralBorrowGraph.RootsCover (childTree s) ∧ (childTree s).indexOfTag s.tracker.global.nextPointerTag = some (GeneralBorrowFreshMetadataChildSlot.index s.slot) at allocated
  have clean := GeneralBorrowForestMixedSharedVacantClean.preserves s.entry.allocation.extra protections s.exprTag s.tracker.global.nextPointerTag true
    s.parent s.primary s.extras s.offset s.len .VisitChildrenOfAccessed s.context s.covered s.tagPresent s.tagFresh s.slot s.fits nonzero s.well bounds
    labels s.allocator registration.2.2.2 s.vacantClean
  have stage := GeneralBorrowForestMixedSharedReleaseData.prepare s.entry.allocation.extra s.tracker {} s.id s.exprTag s.parent s.primary s.extras s.offset s.len
    s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits labels nonzero s.well bounds s.clean s.owned
  let childContext := Classical.choice stage.1
  have bound := GeneralBorrowForestMixedSharedNodeBound.bound s.entry.allocation.extra s.tracker {} s.id s.exprTag s.parent s.primary s.extras s.offset s.len
    s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits labels nonzero s.well bounds s.owned
  have released := GeneralBorrowForestMixedTargetRelease.release s.entry.allocation.extra s.tracker {} s.id s.exprTag s.parent s.primary s.extras s.offset s.len
    s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits labels nonzero s.well bounds s.clean s.owned s.target s.targetActive s.rangePositive
  have frameEq : releasedTree s = {childTree s with locations := (releasedTree s).locations} := released.2.1
  have allocator : GeneralBorrowGcAllocator.Invariant (releasedTree s) := by
    rw [frameEq]
    exact ⟨allocated.1.pool,allocated.1.accounting,allocated.1.unique,allocated.1.nodeTags⟩
  have vacantClean : GeneralBorrowGcVacantClean.VacantClean (releasedTree s) := by
    intro query vacant
    have vacantBefore : (childTree s).nodes.get query = none := by rw [frameEq] at vacant;exact vacant
    have result := GeneralBorrowForestReleaseVacantClean.release_query (childTree s) (held s).global.protectedTags s.tracker.global.nextPointerTag
      (GeneralBorrowFreshMetadataChildSlot.index s.slot) s.primary s.extras (GeneralBorrowFreshMixedChild.extend labels (GeneralBorrowFreshMetadataChildSlot.index s.slot).toNat)
      s.offset (s.offset+s.len) s.rangePositive bound childContext stage.2.2.1 stage.2.2.2.2 stage.2.1 query vacantBefore (clean query vacantBefore)
    exact result.2.2.2
  have restored := GeneralBorrowForestMixedSharedRestoredResources.prepare s.entry.allocation.extra s.tracker {} s.id s.exprTag s.parent s.primary s.extras s.offset s.len
    s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits nonzero s.well bounds s.clean s.owned
    s.target s.targetNode s.targetPresent s.rangePositive s.exprFree s.prefixPath s.exprOutside s.rootPath s.targetActive
  let context := Classical.choice restored.1
  have capacity : (releasedTree s).locations.size = s.entry.allocation.extra.locations.size := released.2.2.2.2.trans allocated.2.2.1
  have nextRoom : (releasedTree s).nodes.size+5 ≤ 4294967295 := by
    have size := allocated.2.2.2.1
    rw [frameEq]
    change (childTree s).nodes.size+5 ≤ 4294967295
    have room := s.room
    omega
  let depth := GeneralBorrowCanonicalParentDepth.normalize (releasedTree s).nodes context.depth
  let normalized : GeneralBorrowForestAccessData.Context (releasedTree s) s.target s.primary s.extras := {context with depth := depth}
  have aligned := GeneralBorrowFreshStagePool.empty_aligned (releasedTree s) allocator.accounting
  have mappingFits : (releasedTree s).tagMapping.deassigned.back? = none → (releasedTree s).tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    change (releasedTree s).nodes.data.size+5 ≤ _ at nextRoom
    omega
  let slot := GeneralBorrowCanonicalParentDepth.slot (releasedTree s) context.depth s.target context.anchorNode context.anchorPresent
    allocator.pool aligned mappingFits
  have future (tag : BorTag) (different : s.tracker.global.nextPointerTag ≠ tag) (fresh : GeneralBorrowTagMap.Fresh s.entry.allocation.extra.tagMapping tag) :
      GeneralBorrowTagMap.Fresh (releasedTree s).tagMapping tag := by
    have lookup := GeneralBorrowForestMixedSharedLookup.lookup s.entry.allocation.extra s.tracker {} s.id s.exprTag s.parent s.primary s.extras s.offset s.len
      s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits labels nonzero s.well bounds s.owned tag different
    apply GeneralBorrowForestForeignSharedFresh.fresh_of_absent
    change (releasedTree s).indexOfTag tag = none
    rw [frameEq]
    change (childTree s).indexOfTag tag = s.entry.allocation.extra.indexOfTag tag at lookup
    change (childTree s).indexOfTag tag = none
    rw [lookup]
    unfold BorrowTree.indexOfTag UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find s.entry.allocation.extra.tagMapping tag fresh]
    rfl
  let data : GeneralBorrowForestEntryValidity.Data (releasedTree s) (ended s).global.protectedTags s.targetNode.tag
      (ended s).global.nextPointerTag s.offset s.len := {
    parent := s.target,primary := s.primary,extras := s.extras,context := normalized,covered := by rw [frameEq];exact allocated.2.2.2.2.1
    tagPresent := restored.2.1,tagFresh := future _ s.different23 s.map3
    globalUnheld := (ended_get s _ s.different23).trans s.unheld3
    nodeTags := allocator.nodeTags,nodeFits := restored.2.2.1,slot := slot,well := released.2.2.2.1,owned := restored.2.2.2.2 }
  have path (location : LocationTree) : ((source_normal_projection (releasedTree s) location (ended s).global.protectedTags).topology.ancestorPath s.target.toNat).getLast! = s.primary.toNat := by
    have inside : s.offset.toNat < (releasedTree s).locations.size.bytes.toNat := by
      rw [capacity,s.allocationSize]
      have positive : 0 < s.len.toNat := s.positive
      have bounds := s.bounds
      omega
    obtain ⟨position,valid,lower,upper⟩ := GeneralRangeMapGeometry.covered (releasedTree s).locations data.well s.offset inside
    have positive := s.rangePositive
    obtain ⟨localData⟩ := data.owned position valid s.rangePositive (by omega) upper
    have root := localData.base.rootPath
    rw [GeneralBorrowFreshMutablePathData.topology_any (releasedTree s) _ location (ended s).global.protectedTags (ended s).global.protectedTags] at root
    exact root
  exact ⟨data,rfl,rfl,rfl,allocator,vacantClean,capacity,released.2.2.1,path,nextRoom,future _ s.different24 s.map4⟩

/-- The real shared FnEntry/len lifetime supplies every raw PC3:0 accepted
suffix field; no post-helper resource or successful-operation input is used. -/
theorem prepare (s : Initial) :
    ∃ input : GeneralBorrowForestAcceptedAfterLen.Initial,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.beforeMachine) (Storage.withCurrent #[] input.caller input.machine) := by
  obtain ⟨root,post,released,trace,rootEq,memoryEq,tracked,releaseEq,mixed,runtime,rootTop⟩ :=
    GeneralBorrowForestAcceptedAfterLenRuntime.executes s.options s.limits s.remaining s.budget s.dispatchFuel s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.entry s.base s.offset s.len s.exprTag s.positive s.nonzero s.signedFits s.bounds #[] s.caller s.machine s.tracker s.enabled s.defaultMode s.fresh s.parent s.primary s.extras s.context s.covered s.tagPresent s.tagFresh s.nodeTags s.unheld s.slot s.fits
      (GeneralBorrowFreshMixedChild.extend (fun _ => true) s.parent.toNat) s.well s.clean s.rangePositive s.owned s.allocationSize s.valid s.live s.uncached s.noClocks s.ghost s.shallow s.cachedAddress s.present s.race s.thread s.index s.current s.active s.top s.presentFrame s.metadata s.notConstructed s.sourceBody s.identity s.callee s.located s.source s.sourceValid s.sourceLive s.sourceCached s.backend s.beforeMachine s.machineEq s.unchecked s.noGc s.fixed
  have releasedEq : releasedTree s = released := by
    change (childTree s).releaseProtector s.tracker.global.nextPointerTag (held s).global.protectedTags = ⟨released,.Released⟩ at releaseEq
    exact congrArg BorrowTree.ProtectorReleaseResult.tree releaseEq
  let r := resources s
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation := s.entry.allocation.setExtra (releasedTree s)}
  have memory : post.memory = RetagEntry.updatedMemory s.beforeMachine.memory s.id s.entry (releasedTree s) := by rw [releasedEq];exact memoryEq
  have found : post.memory.live.find? (fun row => row.1 == s.id) = some (s.id,buffer) := by
    rw [memory]
    exact StackPopRelease.lookup_commit_same s.beforeMachine.memory s.id s.entry (releasedTree s)
  have slotFound : post.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,s.slotEntry) := by
    rw [memory]
    exact StackPopRelease.lookup_commit_other s.beforeMachine.memory s.id s.slotId s.entry s.slotEntry (releasedTree s) s.separate s.slotPresent
  have rootSize : root.locals.size=25 := by rw [rootEq];simp [cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,s.frameSize]
  have keep (i : Nat) (valid : i<root.locals.size) (original : i<s.caller.locals.size) (different : i≠11) :
      root.locals[i]'valid = s.caller.locals[i]'original := by
    simp [rootEq,cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,Array.getElem_set,different,Ne.symm different]
  have keepOpt (i : Nat) (different : i≠11) : root.locals[i]? = s.caller.locals[i]? := by
    simp [rootEq,cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame,Array.getElem?_set,different,Ne.symm different]
  have slot11 : root.locals[11]'(by omega) =
      (⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.len)))),some RootCompilerFacts.usizeLayout⟩ : LocalState Provenance LocalLayout) := by
    simp [rootEq,cachedCaller,LocalPlaces.cachePlaceLayout,writeFrame]
  have accountedAddresses : s.machine.user.addresses = s.beforeMachine.user.addresses := by
    rw [s.machineEq]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    rfl
  obtain ⟨returnThread,returnActive,returnTop⟩ := rootTop rfl
  have zero : root.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [keepOpt 0 (by decide),Array.getElem?_eq_getElem (by have:=s.frameSize;omega)]
    have value := s.live0
    have layout := s.cache0
    cases row : (s.caller.locals[0]'(by have:=s.frameSize;omega)) with
    | mk v l => rw [row] at value layout;cases value;cases layout;rfl
  let input : GeneralBorrowForestAcceptedAfterLen.Initial := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,debug:=s.debugOff,fuel:=s.validityFuel,
    validation:=s.validationEq,dynamicFuel:=s.dynamicFuel,dynamic:=s.fuelEq,cmp:=s.cmp,source:=s.source,budget:=s.budget,dispatch:=s.dispatchFuel,
    caller:=root,machine:=post,id:=s.id,entry:=buffer,base:=s.base,offset:=s.offset,len:=s.len,
    positive:=s.positive,nonzero:=s.nonzero,signedFits:=s.signedFits,bounds:=s.bounds,
    cachedAddress:=by rw [runtime.addresses,←accountedAddresses];exact s.cachedAddress,present:=found,
    parentTag:=s.targetNode.tag,tracker:=ended s,tracked:=tracked,mode:=s.defaultMode,
    ghost:=runtime.ghost,shallow:=runtime.shallow,race:=runtime.race,backend:=runtime.backend,
    clocks:=by rw [rootEq];exact s.noClocks,
    metadata:=by change post.user.payload.payload.user.types.metadata = _;rw [runtime.types];exact s.rootMetadata,
    notConstructed:=by change post.user.payload.payload.user.types.entries.any _ = _;rw [runtime.types];exact s.rootNotConstructed,
    thread:=returnThread,active:=returnActive,top:=returnTop,unchecked:=runtime.unchecked,noGc:=runtime.noGc,fixed:=runtime.fixed,
    size:=rootSize,body:=by rw [rootEq];exact s.sourceBody,identity:=by rw [rootEq];exact s.identity,callee:=by rw [rootEq];exact s.callee,
    track:=by rw [rootEq];exact s.trackNone,relevant:=by rw [rootEq];exact s.relevant,
    immediate:=by
      rw [rootEq]
      change CopyHelperCleanup.AllImmediate (writeFrame (cachedCaller s.caller s.valid) 11 _ _)
      exact CopyHelperCleanup.all_immediate_set _ 11 _ _ (CopyHelperCleanup.all_immediate_cache s.caller 11 RootCompilerFacts.usizeLayout _ s.allImmediate) (by intro memory;simp),
    count:=s.count,countPositive:=s.countPositive,within:=s.within,slot2:=(keepOpt 2 (by decide)).trans s.slot2,
    unused:=by intro index lower upper;rw [keepOpt index (by omega)];exact s.unused index lower upper,
    capacity:=r.capacity.trans s.allocationSize,runtimeContext:=s.ctx,fresh:=s.fresh3,data:=r.data,
    storage:=s.storage,maskValid:=s.maskValid,maskLength:=s.maskLength,initialized:=s.initialized,provenance:=s.provenance,
    storageFits:=s.storageFits,mutable:=s.mutable,bufferExtras:=by rw [runtime.extras];exact s.bufferExtras,bounded:=s.bounded,
    zero:=zero,continuation:=by rw [rootEq];exact s.continuation,varargs:=by rw [rootEq];exact s.varargs,
    context:=s.writeContext,validationContext:=s.validationContext,accessEq:=s.accessEq,validationWidth:=s.validationWidth,
    validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,width:=s.width,runtimeWidth:=s.runtimeWidth,
    runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,slotId:=s.slotId,separate:=s.separate,slot:=s.slotEntry,slotPresent:=slotFound,
    slotRoot:=s.slotRoot,slotChild:=s.slotChild,slotTree:=s.slotTree,slotRootNotHelper:=s.slotRootDifferent3,
    slotRootFree:=s.slotRootFree,slotChildHeld:=s.slotChildHeld,slotDistinct:=s.slotDistinct,slotChildNotHelper:=s.slotChildDifferent3,
    frameTracked:=by rw [rootEq];exact s.frameTracked,slotSize:=s.slotSize,slotStorage:=s.slotStorage,slotMask:=s.slotMask,
    slotProvenance:=s.slotProvenance,slotMutable:=s.slotMutable,place:=s.place,layout:=s.layout,slotBase:=s.slotBase,
    slotPointer:=s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,cached:=by rw [runtime.addresses];exact s.slotCached,
    extras:=by rw [runtime.extras];exact s.slotExtras,destination:=by rw [rootEq];exact s.destination,
    statementFuel:=s.statementFuel,preciseOff:=s.preciseOff,implicitOff:=s.implicitOff,location:=by rw [rootEq],
    valid1:=by change 1 < root.locals.size;rw [rootSize];decide,value1:=by rw [keep 1 (by omega) s.valid1 (by decide)];exact s.value1,
    cached1:=by rw [keep 1 (by omega) s.valid1 (by decide)];exact s.cached1,
    temp12:=(RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.exprTag) (Size.ofBytes (s.base+s.offset))) s.len SharedReferenceMetadata.sharedLayout).imm,
    live12:=by rw [keep 12 (by omega) s.sourceValid (by decide)];exact s.sourceLive,
    live13:=by rw [keep 13 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live13,
    cache13:=by rw [keep 13 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache13,
    live0:=by rw [keep 0 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live0,
    cache0:=by rw [keep 0 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache0,
    live7:=by rw [keep 7 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live7,
    cache7:=by rw [keep 7 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache7,
    dead15:=by rw [keep 15 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.dead15,
    cache15:=by rw [keep 15 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache15,
    dead16:=by rw [keep 16 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.dead16,
    cache16:=by rw [keep 16 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache16,
    live8:=by rw [keep 8 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live8,
    cache8:=by rw [keep 8 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache8,
    live9:=by rw [keep 9 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live9,
    cache9:=by rw [keep 9 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache9,
    live10:=by rw [keep 10 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.live10,
    cache10:=by rw [keep 10 (by omega) (by have:=s.frameSize;omega) (by decide)];exact s.cache10,
    live11:=congrArg LocalState.value slot11,cache11:=congrArg LocalState.layout slot11,
    targetActive:=by rw [r.parent];exact r.active,rootPath:=by rw [r.parent,r.primary];exact r.rootPath,
    targetNotHelper:=s.targetDifferent3,allocator:=r.allocator,vacantClean:=r.vacantClean,room:=r.room,
    freshNext:=s.fresh4,mapFresh:=r.map4,different:=s.different34,
    unheld:=(ended_get s _ s.different24).trans s.unheld4,
    expressionUnheld:=by unfold ProtectedTags.contains;change ((ended s).global.protectedTags.get (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh).global.nextPointerTag).isSome = false;rw [ended_get s _ s.different23,s.unheld3];rfl,
    targetDifferent:=s.targetDifferent4,rootDifferent:=s.slotRootDifferent4,childDifferent:=s.slotChildDifferent4 }
  exact ⟨input,rfl,rfl,rfl,rfl,trace⟩

/-- Starting at the actual ROOT shared-expression boundary, execute protected
shared FnEntry, len and real protector lifetime, the accepted guard, mutable
expression/as_mut_ptr, adjacent physical copy and a physical true return.
Every permitted reachable finite Unit-choice prefix succeeds. -/
theorem invoke (s : Initial) :
    let cfg := config s.options (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] s.caller s.beforeMachine
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
  obtain ⟨input,options,limits,remaining,span,leadingTrace⟩ := prepare s
  obtain ⟨ready,finalState,physical,suffix,terminal,empty,_,_⟩ := GeneralBorrowForestAcceptedAfterLen.invoke input
  rw [options,limits,remaining,span] at suffix terminal
  have full := SuccessfulTrace.append leadingTrace suffix
  have safety := SuccessfulTrace.no_ub
    (⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 (Storage.withCurrent #[] s.caller s.beforeMachine) finalState ⟨by decide,rfl⟩ full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨ready,finalState,physical,full,terminal,empty,safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩

end
end DuplicatePrefix.GeneralBorrowForestAcceptedAfterLenHelper
