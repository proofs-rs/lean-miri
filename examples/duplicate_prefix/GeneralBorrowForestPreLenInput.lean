import duplicate_prefix.GeneralBorrowForestRejectedAfterLen
namespace DuplicatePrefix.GeneralBorrowForestPreLenInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
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
  slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 inputCount)))),some RootCompilerFacts.usizeLayout⟩
  unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩
  trackNone : caller.trackCallerArg = none
  relevant : caller.extra.userRelevance > 0
  rootMetadata : beforeMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  rootNotConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false

end
end DuplicatePrefix.GeneralBorrowForestPreLenInput
