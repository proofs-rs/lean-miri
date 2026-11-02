import duplicate_prefix.GeneralBorrowExposedScopedWritableLenCallReturnReadWriteReady
import duplicate_prefix.GeneralBorrowExposedScopedSharedPathMetadata
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableLenCallInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
/-- Intermediate physical/source len-call data, formed by the original caller
prefix. It contains no operation-success or post-helper resource field. -/
structure Input where
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
  frames : Array CompilerFrameContext.ActualFrame
  caller : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracker : MachineHooks.BorrowState
  enabled : machine.borrowTracker = some tracker
  defaultMode : tracker.retagMode = .Default
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  input : GeneralBorrowFreshMetadataChildShared.Input
  selected : UniIndex
  head : UniIndex
  tail : List UniIndex
  writable : Nat → Bool
  raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags selected head tail writable
  treeEq : input.tree=entry.allocation.extra
  parentTagEq : input.parentTag=exprTag
  tagEq : input.newTag=tracker.global.nextPointerTag
  offsetEq : input.offset=offset
  lenEq : input.len=len
  protectedEq : input.isProtected=true
  atBase : input.offset=0
  full : input.len=input.tree.locations.size.bytes
  rangePositive : input.offset.toNat < (input.offset+input.len).toNat
  clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildShared.index input)=none) input.tree.locations
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
  top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
        (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index
  presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
        (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current
  metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
        (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime
  notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
        (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false
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
  first : GeneralBorrowFreshMetadataChildShared.Input
  firstTags : ProtectedTags
  firstRaw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources first firstTags selected head tail (fun _=>true)
  firstAtBase : first.offset=0
  firstFull : first.len=first.tree.locations.size.bytes
  firstTreeEq : input.tree=GeneralBorrowExposedScopedSharedPathMetadata.child first firstTags .VisitChildrenOfAccessed
  firstParentEq : input.parent=GeneralBorrowFreshMetadataChildShared.index first
  writableEq : writable=GeneralBorrowFreshMixedChild.extend (fun _=>true) (GeneralBorrowFreshMetadataChildShared.index first).toNat
  initialTags : GeneralBorrowGcAllocator.NodeTags first.tree
  exprUnheld : (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags.contains input.parentNode.tag=false

theorem executes (s : Input)
 :
    let childTree := GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag
    ∃ (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (released : BorrowTree),
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent s.frames s.caller s.beforeMachine) (Storage.withCurrent s.frames root post) ∧
      root={writeFrame (cachedCaller s.caller s.valid) 11 (.scalar (.fromScalarInt (.ofUInt64 s.len)))
        (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using s.valid) with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory s.beforeMachine.memory s.id s.entry released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      childTree.releaseProtector s.tracker.global.nextPointerTag held.global.protectedTags=⟨released,.Released⟩ ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location held.global.protectedTags
        (GeneralBorrowFreshMetadataChildShared.index s.input) s.selected s.head s.tail
        (fun position => s.raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index s.input).toNat)
        (GeneralBorrowFreshMixedChild.extend s.writable (GeneralBorrowFreshMetadataChildShared.index s.input).toNat)))
        s.offset (s.offset+s.len) released.locations ∧
      released.locations.WellFormed ∧ released.locations.size=s.entry.allocation.extra.locations.size ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts s.options s.remaining s.span s.beforeMachine post ∧
      (s.frames=#[] → GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.beforeMachine post) ∧
      post.memory.live.find? (fun row=>row.1==s.id)=some (s.id,{s.entry with allocation:=s.entry.allocation.setExtra released}) ∧
      GeneralBorrowGcAllocator.NodeTags released ∧
      ∃ writeContext : GeneralBorrowExposedKnownRootRangeData.Context released s.first.parent s.selected s.head s.tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
          (held.global.endCall borrowFrame).protectedTags s.first.parent s.selected s.head s.tail .Write)) s.offset (s.offset+s.len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location
          (held.global.endCall borrowFrame).protectedTags) s.offset (s.offset+s.len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released location
          (held.global.endCall borrowFrame).protectedTags s.first.parent s.selected s.head s.tail .Read)) s.offset (s.offset+s.len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location
          (held.global.endCall borrowFrame).protectedTags s.first.parent s.selected s.head s.tail
          (fun position=>s.raw.component.support position ∨position=(GeneralBorrowFreshMetadataChildShared.index s.input).toNat)
          (fun _=>true))) s.offset (s.offset+s.len) released.locations := by
  exact GeneralBorrowExposedScopedWritableLenCallReturnReadWriteReady.executes
    s.options s.limits s.remaining s.budget s.dispatchFuel s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.entry s.base s.offset s.len s.exprTag s.positive s.nonzero s.signedFits s.bounds s.frames s.caller s.machine s.tracker s.enabled s.defaultMode s.fresh s.input s.selected s.head s.tail s.writable s.raw s.treeEq s.parentTagEq s.tagEq s.offsetEq s.lenEq s.protectedEq s.atBase s.full s.rangePositive s.clean s.allocationSize s.valid s.live s.uncached s.noClocks s.ghost s.shallow s.cachedAddress s.present s.race s.thread s.index s.current s.active s.top s.presentFrame s.metadata s.notConstructed s.sourceBody s.identity s.callee s.located s.source s.sourceValid s.sourceLive s.sourceCached s.backend s.beforeMachine s.machineEq s.unchecked s.noGc s.fixed s.first s.firstTags s.firstRaw s.firstAtBase s.firstFull s.firstTreeEq s.firstParentEq s.writableEq s.initialTags s.exprUnheld
end
end DuplicatePrefix.GeneralBorrowExposedScopedWritableLenCallInput
