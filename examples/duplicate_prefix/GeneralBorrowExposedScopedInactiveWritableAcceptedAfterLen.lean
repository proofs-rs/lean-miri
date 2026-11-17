import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAcceptedExpression
import duplicate_prefix.GeneralBorrowExposedScopedAcceptedControl
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure InitialFor (profileMode : ProfileMode) where
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
  data : GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw.DataFor entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail profileMode
  rangePositive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat
  vacantClean : GeneralBorrowGcVacantClean.VacantClean entry.allocation.extra
  nextFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value<18446744073709551615
  futureFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  different : tracker.global.nextPointerTag≠(ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  room : entry.allocation.extra.nodes.size+2<65536
  valid1 : (1 : MIR.LocalId)<caller.locals.size
  live1 : caller.locals[1].value=.live (.immediate (RetagReferencePlace.sliceValue
    (ActualReferenceContext.config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)
  cached1 : caller.locals[1].layout=some ActualReferenceMetadata.reference
  count : UInt64
  countPositive : (0 : UInt64)<count
  within : count≤len/2
  frameFacts : GeneralBorrowExposedScopedAcceptedControl.FrameFacts caller len count
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

/-- Legacy global accepted-control interface. -/
abbrev Initial := InitialFor .global

def machine {profileMode : ProfileMode} (s : InitialFor profileMode) := GeneralBorrowExposedScopedAcceptedControl.machine s.options s.remaining s.span s.machine

structure MachineFacts {profileMode : ProfileMode} (s : InitialFor profileMode) : Prop where
  memory : (machine s).memory=s.machine.memory
  tracked : (machine s).borrowTracker=s.machine.borrowTracker
  race : (machine s).dataRace=s.machine.dataRace
  threads : (machine s).threads=s.machine.threads
  addresses : (machine s).user.addresses=s.machine.user.addresses
  types : (machine s).user.payload.payload.user.types=s.machine.user.payload.payload.user.types
  extras : (machine s).user.payload.payload.user.runtime.extras=s.machine.user.payload.payload.user.runtime.extras
  backend : (machine s).user.payload.payload.user.backend=s.machine.user.payload.payload.user.backend

theorem machine_facts {profileMode : ProfileMode} (s : InitialFor profileMode) : MachineFacts s := by
  constructor <;> unfold machine GeneralBorrowExposedScopedAcceptedControl.machine RootZeroCompleteState.tick SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
  all_goals rfl

structure Origin {profileMode : ProfileMode} (s : InitialFor profileMode) (ready : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode) : Prop where
  options : ready.options=s.options
  limits : ready.limits=s.limits
  remaining : ready.remaining=s.remaining
  span : ready.span=s.span
  id : ready.id=s.id
  entry : ready.entry=s.entry
  parentTag : ready.parentTag=s.parentTag
  base : ready.base=s.base
  offset : ready.offset=s.offset
  len : ready.len=s.len
  tracker : ready.tracker=s.tracker
  machine : ready.machine=machine s
  data : HEq ready.data s.data
  frame : GeneralBorrowExposedScopedAcceptedControl.Result s.caller ready.caller
  kept : GenericLenAcceptedPrelude.FrameFacts s.caller ready.caller

theorem prepare {profileMode : ProfileMode} (s : InitialFor profileMode) :
    ∃ ready : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode,
      Origin s ready ∧
      SuccessfulTrace.Trace (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] ready.caller ready.machine) := by
  obtain ⟨frame,trace,facts,kept⟩:=GeneralBorrowExposedScopedAcceptedControl.executes s.options s.limits s.remaining s.span
    s.source s.debug s.fuel s.validation s.caller s.machine s.len s.count s.countPositive s.within s.frameFacts
    s.tracker s.tracked s.mode s.ghost s.shallow s.unchecked s.noGc s.fixed
  have mf:=machine_facts s
  have valid15 : (15 : MIR.LocalId)<frame.locals.size := by rw [facts.size];decide
  have valid16 : (16 : MIR.LocalId)<frame.locals.size := by rw [facts.size];decide
  have valid1 : (1 : MIR.LocalId)<frame.locals.size := by rw [facts.size];decide
  have row15 : frame.locals[15]'valid15=⟨.live (.immediate .uninit),none⟩ := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans facts.slot15)
  have row16 : frame.locals[16]'valid16=⟨.live (.immediate .uninit),none⟩ := Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans facts.slot16)
  have row1 : frame.locals[1]'valid1=s.caller.locals[1]'s.valid1 := Option.some.inj
    ((Array.getElem?_eq_getElem valid1).symm.trans (facts.slot1.trans (Array.getElem?_eq_getElem s.valid1)))
  have nextGhost : (machine s).user.payload.ghost=false :=
    (RootZeroCompleteState.tick_ghost s.options s.remaining s.span _).trans ((RootZeroCompleteState.tick_ghost s.options s.remaining s.span s.machine).trans s.ghost)
  have nextShallow : (machine s).user.payload.validation=.Shallow :=
    (RootZeroCompleteState.tick_shallow s.options s.remaining s.span _).trans ((RootZeroCompleteState.tick_shallow s.options s.remaining s.span s.machine).trans s.shallow)
  let ready : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,ctx:=s.ctx,precise:=s.precise,implicitWrites:=s.implicitWrites,
    debug:=s.debug,dynamicFuel:=s.dynamicFuel,dynamic:=s.dynamic,fuel:=s.fuel,validation:=s.validation,cmp:=s.cmp,source:=s.source,budget:=s.budget,dispatch:=s.dispatch,
    caller:=frame,machine:=machine s,id:=s.id,entry:=s.entry,parentTag:=s.parentTag,base:=s.base,offset:=s.offset,len:=s.len,
    positive:=s.positive,nonzero:=s.nonzero,signedFits:=s.signedFits,bounds:=s.bounds,capacity:=s.capacity,
    cachedAddress:=by rw [mf.addresses];exact s.cachedAddress,present:=by rw [mf.memory];exact s.present,
    tracker:=s.tracker,tracked:=mf.tracked.trans s.tracked,mode:=s.mode,fresh:=s.fresh,selected:=s.selected,head:=s.head,tail:=s.tail,data:=s.data,
    rangePositive:=s.rangePositive,vacantClean:=s.vacantClean,nextFresh:=s.nextFresh,futureFresh:=s.futureFresh,different:=s.different,room:=s.room,
    valid15:=valid15,live15:=congrArg LocalState.value row15,uncached15:=congrArg LocalState.layout row15,
    valid16:=valid16,live16:=congrArg LocalState.value row16,uncached16:=congrArg LocalState.layout row16,
    valid1:=valid1,live1:=(congrArg LocalState.value row1).trans s.live1,cached1:=(congrArg LocalState.layout row1).trans s.cached1,
    body:=facts.body.trans s.frameFacts.body,identity:=facts.identity.trans s.frameFacts.identity,callee:=facts.callee.trans s.frameFacts.callee,
    location:=facts.location,clocks:=by rw [facts.extra];exact s.frameFacts.clocks,
    ghost:=nextGhost,shallow:=nextShallow,race:=mf.race.trans s.race,backend:=mf.backend.trans s.backend,
    metadata:=by rw [mf.types];exact s.metadata,notConstructed:=by rw [mf.types];exact s.notConstructed,
    thread:=s.thread,active:=by rw [mf.threads];exact s.active,top:=s.top,
    unchecked:=(RootZeroCompleteState.tick_flags s.options s.remaining s.span _).1.trans ((RootZeroCompleteState.tick_flags s.options s.remaining s.span s.machine).1.trans s.unchecked),
    noGc:=(RootZeroCompleteState.tick_flags s.options s.remaining s.span _).2.trans ((RootZeroCompleteState.tick_flags s.options s.remaining s.span s.machine).2.trans s.noGc),
    fixed:=by rw [mf.threads];exact s.fixed }
  exact ⟨ready,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,facts,kept⟩,trace⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen
