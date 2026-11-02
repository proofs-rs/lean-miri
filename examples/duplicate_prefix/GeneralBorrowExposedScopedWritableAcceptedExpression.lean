import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultEntryRaw
import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutCallReturnReady
import duplicate_prefix.GeneralBorrowExposedScopedDefaultExpression
import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultData
import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultNext
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableAcceptedExpression
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Input where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  ctx : ActualReferenceContext.Context options remaining span
  precise : options.retag.preciseInteriorMut=false
  implicitWrites : options.retag.implicitWrites=false
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
  data : GeneralBorrowExposedScopedWritableDefaultEntryRaw.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail
  atBase : data.input.offset=0
  full : data.input.len=data.input.tree.locations.size.bytes
  rangePositive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  nextFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value<18446744073709551615
  futureFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  different : tracker.global.nextPointerTag≠(ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  room : entry.allocation.extra.nodes.size+2<65536
  valid15 : (15 : MIR.LocalId)<caller.locals.size
  live15 : caller.locals[15].value=.live (.immediate .uninit)
  uncached15 : caller.locals[15].layout=none
  valid16 : (16 : MIR.LocalId)<caller.locals.size
  live16 : caller.locals[16].value=.live (.immediate .uninit)
  uncached16 : caller.locals[16].layout=none
  valid1 : (1 : MIR.LocalId)<caller.locals.size
  live1 : caller.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
    (ActualReferenceContext.config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)
  cached1 : caller.locals[1].layout=some ActualReferenceMetadata.reference
  body : caller.body=RootBody.reflected.body.body
  identity : caller.bodyIdentity=RootBody.reflected.body.identity
  callee : caller.functionInstance=RootBody.reflected.functionInstance
  location : caller.location=.mir ⟨6,7⟩
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

def expressionTree (s : Input) := (GeneralBorrowExposedScopedDefaultExpression.child s.entry.allocation.extra s.tracker.global.protectedTags
  s.parentTag s.tracker.global.nextPointerTag s.offset s.len .VisitChildrenOfAccessed).tree

def value (s : Input) := (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
  (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm

def expressionFrame (s : Input) := CopyHelperSteps.advance
  (ActualLocalCopy.written s.caller 16 ActualReferenceMetadata.reference s.valid16 (value s)) ⟨6,7⟩

def expressionTracker (s : Input) := ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh

def expressionMachine (s : Input) := {ReferenceBorrowDriver.allocatedMachine s.machine s.tracker s.fresh with
  memory:=RetagEntry.updatedMemory s.machine.memory s.id s.entry (expressionTree s)}

def expressionEntry (s : Input) : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  {s.entry with allocation:=s.entry.allocation.setExtra (expressionTree s)}

theorem step (s : Input) :
    ExecutionMachine.step (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] s.caller s.machine)=(Storage.withCurrent #[] (expressionFrame s) (expressionMachine s),.ok true) := by
  obtain ⟨context,owned⟩:=GeneralBorrowExposedScopedWritableDefaultData.build s.data.input s.tracker.global.protectedTags
    s.selected s.head s.tail s.data.resources
  rw [s.data.treeEq] at context
  simp only [s.data.treeEq,s.data.offsetEq,s.data.lenEq] at owned
  have mixedOwned : GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data s.entry.allocation.extra location s.tracker.global.protectedTags
        s.data.input.parent s.selected s.head s.tail s.data.resources.component.support (fun _=>true)))
      s.offset (s.offset+s.len) s.entry.allocation.extra.locations := by
    intro position valid positive lower upper
    obtain ⟨row⟩:=owned position valid positive lower upper
    exact ⟨row.base⟩
  exact GeneralBorrowExposedScopedDefaultExpression.positive_statement s.options s.limits s.remaining s.span s.precise s.implicitWrites
    s.debug s.cmp s.dynamicFuel s.fuel s.dynamic s.validation s.base s.offset s.len s.id s.entry s.positive s.nonzero s.signedFits
    #[] s.caller s.machine s.body s.identity s.callee s.location s.tracker s.tracked s.mode s.fresh s.parentTag s.data.input.parent s.selected s.head s.tail
    context (by rw [←s.data.treeEq];exact s.data.input.covered)
    (by simpa only [s.data.treeEq,s.data.parentTagEq,BorrowTree.indexOfTag] using s.data.input.parentTagPresent)
    (by simpa only [s.data.treeEq,s.data.newTagEq] using s.data.input.fresh)
    (by rw [←s.data.treeEq];exact s.data.resources.forest)
    (by rw [←s.data.treeEq];exact s.data.input.noFree) (by rw [←s.data.treeEq];exact s.data.input.aligned)
    (by rw [←s.data.treeEq];exact s.data.input.fits) s.data.resources.component.support
    (by rw [←s.data.treeEq];exact s.data.input.well) (by rw [s.capacity];exact s.bounds) s.capacity mixedOwned
    s.valid1 s.valid16 s.live1 s.cached1 s.live16 s.uncached16 s.clocks s.ghost s.shallow s.cachedAddress s.present s.race
    s.metadata s.notConstructed
end
end DuplicatePrefix.GeneralBorrowExposedScopedWritableAcceptedExpression
