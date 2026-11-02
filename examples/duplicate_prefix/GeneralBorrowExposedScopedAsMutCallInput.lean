import duplicate_prefix.GeneralBorrowExposedScopedAsMutInitializedComplete
import duplicate_prefix.GeneralBorrowForestAsMutEntryState
import duplicate_prefix.GenericAsMutCallFrontend
import duplicate_prefix.GenericAsMutReturnState
import duplicate_prefix.GenericSharedLenAccepted
namespace DuplicatePrefix.GeneralBorrowExposedScopedAsMutCallInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
set_option autoImplicit false in
structure Input where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  ctx : ActualReferenceContext.Context options remaining span
  debug : options.place.debugAssertions=false
  dynamicFuel : Nat
  dynamic : options.place.dynamicFuel=dynamicFuel+1
  fuel : Nat
  validation : options.limits.validation=fuel+1
  cmp : ProjectionMetadataFacts.NullComparator
  source : PreparedContracts.SourceComparator
  budget : Nat
  dispatch : limits.callDispatch=budget+1
  caller : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  parentTag : BorTag
  base : UInt64
  offset : UInt64
  len : UInt64
  positive : (0 : UInt64)<len
  nonzero : base+offset≠0
  signedFits : len.toNat<9223372036854775808
  bounds : offset.toNat+len.toNat≤entry.allocation.byteSize.bytes.toNat
  capacity : entry.allocation.extra.locations.size=entry.allocation.byteSize
  cachedAddress : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩
  present : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker=some tracker
  mode : tracker.retagMode=.Default
  fresh : tracker.global.nextPointerTag.value<18446744073709551615
  selected : UniIndex
  head : UniIndex
  tail : List UniIndex
  data : GeneralBorrowExposedScopedMutableEntryRaw.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail
  atBase : data.input.offset=0
  full : data.input.len=data.input.tree.locations.size.bytes
  rangePositive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat
  clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildDefault.index data.input)=none) data.input.tree.locations
  valid15 : (15 : MIR.LocalId)<caller.locals.size
  live15 : caller.locals[15].value=.live (.immediate .uninit)
  uncached15 : caller.locals[15].layout=none
  valid16 : (16 : MIR.LocalId)<caller.locals.size
  live16 : caller.locals[16].value=.live (.immediate (RetagReferencePlace.sliceValue
    (ActualReferenceContext.config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)
  cached16 : caller.locals[16].layout=some ActualReferenceMetadata.reference
  body : caller.body=RootBody.reflected.body.body
  identity : caller.bodyIdentity=RootBody.reflected.body.identity
  callee : caller.functionInstance=RootBody.reflected.functionInstance
  location : caller.location=.mir ⟨6,8⟩
  clocks : caller.extra.dataRace=none
  ghost : machine.user.payload.ghost=false
  shallow : machine.user.payload.validation=.Shallow
  race : machine.dataRace=none
  backend : machine.user.payload.payload.user.backend=.none
  metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime
  notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty==4)=false
  thread : ThreadRecord
  active : machine.threads.activeThread?=some thread
  top : thread.topUserRelevantFrame=some 0
  unchecked : ((ActualReferenceContext.config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false
  noGc : ((ActualReferenceContext.config options (remaining+1) span).terminators.getControl machine.user).gcInterval=0
  fixed : machine.threads.fixedScheduling=true

def caller (s : Input) := AsMutUncachedCall.cachedCaller s.caller s.valid15
def accounted (s : Input) := AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine
def initial (s : Input) := Storage.withCurrent #[] (caller s) (accounted s)
def destination (s : Input) := (LocalPlaces.localRuntimePlace 0 (caller s) 15 CopyCompilerFacts.destPointerLayout).stackView
def parent (s : Input) := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
  (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
def pushed (s : Input) := (AsMutPush.completed s.options.userRelevantCrates (initial s) (destination s) (caller s)).machine
def held (s : Input) := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag
def childTree (s : Input) := GeneralBorrowExposedScopedMutableArgumentRaw.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
def after (s : Input) :=
  {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine (pushed s) s.tracker s.fresh)
    (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag with
    memory:=RetagEntry.updatedMemory (pushed s).memory s.id s.entry (childTree s)}
def adjusted (s : Input) := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
  (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
def helper (s : Input) := GeneralBorrowExposedScopedAsMutEntry.initialized s.options (initial s) (destination s) (parent s) (adjusted s) s.id s.tracker.global.nextPointerTag
def inside (s : Input) : LocalAllocation Provenance BorrowTree MiriMemoryKind := {s.entry with allocation:=s.entry.allocation.setExtra (childTree s)}
end
end DuplicatePrefix.GeneralBorrowExposedScopedAsMutCallInput
