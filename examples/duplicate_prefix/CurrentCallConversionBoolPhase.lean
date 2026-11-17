import duplicate_prefix.CurrentCallConversionBool
import duplicate_prefix.CurrentCallOrdinaryConversionEnsure

/-! The shared selected Bool phase. The converter is derived from the initial
selected protocol at the actual saved-tag registration state, then consumed by
the existing typed Bool proof. Source families are not part of this interface. -/
namespace DuplicatePrefix.CurrentCallConversionBoolPhase
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext CurrentCallResourceNormalization CandidateStableCallOwnership
open CurrentCallOrdinaryInput CurrentCallConversionSourceCopy TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
noncomputable section

/-- Current descriptor and physical data before the one actual Bool tag
allocation. These are representation facts, not operation outcomes. -/
structure CurrentData (machine : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (place : MPlaceTy Provenance) where
  enabled : machine.borrowTracker=some tracker
  frameBorrow : frame.extra.borrowTracker=some borrowFrame
  fresh : tracker.global.nextPointerTag.value<18446744073709551615
  family : CurrentCallSpatialCover.Family
  root : BorTag
  source : Allocation CtfeProvenance Unit
  base : UInt64
  offset : UInt64
  value : family.value=Pointer.new (.concrete family.allocation root) (Size.ofBytes (base+offset))
  physicalPointer : place.mplace.ptr=family.value.withOptionalProvenance
  layout : place.layout=RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned=none
  physical : Physical source offset 1 false
  current : CurrentPayload machine family.allocation source
  absent : machine.memory.live.find? (fun row=>row.1==family.allocation)=none
  noFunction : machine.memory.hasFunctionPointer family.allocation=false
  noVaList : machine.memory.hasVaListId family.allocation=false
  cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩
  rootCached : tracker.global.rootTag? family.allocation=some root
  addressRoom : base.toNat+source.len<2^64
  nonnull : base+offset≠0
  rootBelow : root.value.toNat<tracker.global.nextPointerTag.value.toNat
  protectors : ∀row∈tracker.global.protectedTags.entries,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat
  registry : machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==family.allocation)=false
  race : machine.dataRace=none
  ghost : machine.user.payload.ghost=false
  backend : machine.user.payload.payload.user.backend=.none

namespace CurrentData
variable {machine tracker frames frame borrowFrame place}
def registered (D : CurrentData machine tracker frames frame borrowFrame place) : RootState :=
  registeredState frames frame borrowFrame (allocatedMachine machine tracker D.fresh)
    (allocatedTracker tracker D.fresh) D.family.allocation tracker.global.nextPointerTag
def next (D : CurrentData machine tracker frames frame borrowFrame place) : MachineHooks.BorrowState :=
  registeredTracker (allocatedTracker tracker D.fresh) tracker.global.nextPointerTag
theorem current_registered (D : CurrentData machine tracker frames frame borrowFrame place) :
    CurrentPayload D.registered.machine D.family.allocation D.source := by
  cases D.current with
  | memory descriptor=>exact .memory descriptor
  | internalStatic definition descriptor initializer=>exact .internalStatic definition descriptor initializer
end CurrentData

variable {options : EvalConfigurationCore.Options} {remaining inputRemaining : Nat} {span : PreparedContracts.FixedSpanQuery}
variable {machine : Before} {tracker : MachineHooks.BorrowState}
variable {frames : Array CompilerFrameContext.ActualFrame} {frame : CompilerFrameContext.ActualFrame}
variable {borrowFrame : FrameState} {place : MPlaceTy Provenance}

/-- Exact typed protection output, retaining the actual finite-converter result
and its whole post-machine expression for both entry consumers. -/
structure Protected (D : CurrentData machine tracker frames frame borrowFrame place)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (charge reserve : Nat) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState)
    (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
      tail charge reserve finalAddresses finalTape) where
  post : RootState
  output : CurrentCallPostEntryCheckpoint.Return post.machine {D.next with global:=result.global} place
  actual : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
    (Storage.withCurrent frames frame machine)=.ok () post
  id : output.id=D.family.allocation
  offset : output.offset=D.offset.toNat
  original : output.original=D.family.at allocationRoot
  tag : output.node.tag=tracker.global.nextPointerTag
  nodes : output.window.allocation.extra.nodes.size≤2
  tracked : post.machine.borrowTracker=some {D.next with global:=result.global}
  stack : post.stack=(Storage.withCurrent frames
    (registeredFrame frame borrowFrame D.family.allocation tracker.global.nextPointerTag) machine).stack
  machineEq : post.machine={childMachine options result.machine D.family.allocation D.root tracker.global.nextPointerTag result.converted
      result.global.protectedTags D.offset 1 with memory:=
    {(childMachine options result.machine D.family.allocation D.root tracker.global.nextPointerTag result.converted
      result.global.protectedTags D.offset 1).memory with live:=
      (((childMachine options result.machine D.family.allocation D.root tracker.global.nextPointerTag result.converted
        result.global.protectedTags D.offset 1).memory.live.filter (fun row=>row.1!=D.family.allocation)).push
          (D.family.allocation,⟨.machine .global,output.window.allocation⟩))}}

theorem of_result (ctx : ActualRetagContext.Context options remaining span)
    (D : CurrentData machine tracker frames frame borrowFrame place)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (tail : List AllocId) (charge reserve : Nat) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState)
    (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
      tail charge reserve finalAddresses finalTape) :
    Nonempty (Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) := by
  have conversion : Allocation.adjustFromTcx D.source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state=>.ok (AllocationCopy.snapshot D.source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer D.registered.machine=.ok result.converted result.machine := by
    rw [wiring];exact result.completed
  have enabled : result.machine.borrowTracker=some {D.next with global:=result.global} := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  have cached : result.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==D.family.allocation)=some ⟨D.family.allocation,D.base⟩ := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
    exact result.bases _ _ D.cached
  have root : result.global.rootTag? D.family.allocation=some D.root := result.roots _ _ D.rootCached
  have race : result.machine.dataRace=none := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.race
  have ghost : result.machine.user.payload.ghost=false := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.ghost
  have backend : result.machine.user.payload.payload.user.backend=.none := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.backend
  have registry : result.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==D.family.allocation)=false := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.registry
  obtain ⟨post,R,actual,id,offset,original,tag,nodes,tracked,stack,machineEq⟩:=
    CurrentCallConversionBool.latent options remaining span ctx frames frame borrowFrame D.frameBorrow
      machine tracker D.enabled D.fresh D.family D.root D.source D.base D.offset place D.value D.physicalPointer
      D.layout D.aligned D.physical D.current D.absent D.noFunction D.noVaList D.cached D.rootCached D.addressRoom
      D.nonnull D.rootBelow D.protectors result.converted result.attributes result.wellFormed result.machine
      {D.next with global:=result.global} conversion enabled root cached race ghost backend registry result.flags result.counter
  exact ⟨⟨post,R,actual,id,offset,original,tag,nodes,tracked,stack,machineEq⟩⟩

/-- Pure initial-phase frames at the actual saved-B registration state. -/
structure FirstPhase {limits before argument length}
    (input : OrdinaryInput options limits inputRemaining span before argument length place)
    (D : CurrentData machine tracker frames frame borrowFrame place) where
  infoEq : ∀id,D.registered.machine.memory.getAllocInfo id=before.memory.getAllocInfo id
  addresses : D.registered.machine.user.addresses=before.user.addresses
  tape : EvalPointerSource.tape.get D.registered.machine=EvalPointerSource.tape.get before
  thread : D.registered.machine.threads.activeThread=before.threads.activeThread
  roots : ∀id,D.next.global.rootTag? id=input.tracker.global.rootTag? id
  spent : Nat
  reserve : Nat
  room : spent+reserve≤16
  positive : 0<reserve
  counter : D.next.global.nextPointerTag.value.toNat≤input.tracker.global.nextPointerTag.value.toNat+spent
  metadata : ∀id∈CurrentCallConversionPlan.selectedIds before argument length place,RelocationTargetMetadata D.registered.machine id
  rest : List (Allocation CtfeProvenance Unit)
  head : CurrentCallConversionPlan.selectedPayloads before argument length place=D.source::rest

theorem first {limits before argument length}
    (input : OrdinaryInput options limits inputRemaining span before argument length place)
    (ctx : ActualRetagContext.Context options remaining span)
    (D : CurrentData machine tracker frames frame borrowFrame place)
    (phase : FirstPhase input D) :
    ∃externStatic,
      (CurrentCallConversionActualEnsure.hooks options).rootPointer=
        PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic ∧
    ∃finalAddresses finalTape,
    ∃result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
      (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve finalAddresses finalTape,
      Nonempty (Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic
        (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve finalAddresses finalTape result) := by
  obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,_⟩:=CurrentCallOrdinaryConversionEnsure.first input
    D.registered D.next phase.infoEq phase.addresses phase.tape phase.thread phase.roots phase.spent phase.reserve
    phase.room phase.positive phase.counter (by rfl) phase.metadata D.family.allocation D.root D.source phase.rest phase.head
    D.current_registered D.absent D.rootCached D.registry D.race
  exact ⟨externStatic,wiring,finalAddresses,finalTape,result,of_result ctx D externStatic wiring _ _ _ _ _ result⟩

/-- Pure continuation frames after the SAME first converter result. -/
structure NextPhase {limits before argument length}
    (input : OrdinaryInput options limits inputRemaining span before argument length place)
    (D : CurrentData machine tracker frames frame borrowFrame place) where
  initial : Before
  oldTracker : MachineHooks.BorrowState
  firstSource : Allocation CtfeProvenance Unit
  rest : List (Allocation CtfeProvenance Unit)
  head : CurrentCallConversionPlan.selectedPayloads before argument length place=firstSource::D.source::rest
  externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance)
  wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
    PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic
  oldReserve : Nat
  finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState
  finalTape : ExecutionChoices.Tape
  previous : CurrentCallConversionFiniteFold.Result firstSource PreparedReflection.actual.compiler.runtime.target.base
    (CurrentCallConversionActualEnsure.hooks options).address externStatic initial oldTracker
    (CurrentCallConversionFiniteFold.targets D.source++rest.flatMap CurrentCallConversionFiniteFold.targets)
    (addressCharge before) oldReserve finalAddresses finalTape
  initialInfo : ∀id,initial.memory.getAllocInfo id=before.memory.getAllocInfo id
  infoEq : ∀id,D.registered.machine.memory.getAllocInfo id=initial.memory.getAllocInfo id
  addresses : D.registered.machine.user.addresses=previous.addresses
  tape : EvalPointerSource.tape.get D.registered.machine=previous.tape
  thread : D.registered.machine.threads.activeThread=initial.threads.activeThread
  roots : ∀id,D.next.global.rootTag? id=previous.global.rootTag? id
  spent : Nat
  reserve : Nat
  room : spent+reserve≤oldReserve
  positive : 0<reserve
  counter : D.next.global.nextPointerTag.value.toNat≤previous.global.nextPointerTag.value.toNat+spent
  bases : ∀id base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base→
    D.registered.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base
  metadata : ∀id∈CurrentCallConversionFiniteFold.targets D.source,RelocationTargetMetadata D.registered.machine id

theorem next {limits before argument length}
    (input : OrdinaryInput options limits inputRemaining span before argument length place)
    (ctx : ActualRetagContext.Context options remaining span)
    (D : CurrentData machine tracker frames frame borrowFrame place)
    (phase : NextPhase input D) :
    ∃result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address phase.externStatic D.registered.machine D.next
      (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve phase.finalAddresses phase.finalTape,
      Nonempty (Protected (options:=options) (remaining:=remaining) (span:=span) D phase.externStatic
        (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve phase.finalAddresses phase.finalTape result) := by
  obtain ⟨result,_⟩:=CurrentCallOrdinaryConversionEnsure.next input phase.initial phase.oldTracker phase.firstSource D.source
    phase.rest phase.head phase.externStatic phase.wiring phase.oldReserve phase.finalAddresses phase.finalTape phase.previous
    D.registered D.next phase.initialInfo phase.infoEq phase.addresses phase.tape phase.thread phase.roots
    phase.spent phase.reserve phase.room phase.positive phase.counter (by rfl) phase.bases phase.metadata D.family.allocation
    D.root D.current_registered D.absent D.rootCached D.registry D.race
  exact ⟨result,of_result ctx D phase.externStatic phase.wiring _ _ _ _ _ result⟩

/-- Extract the concrete CURRENT Bool descriptor and pointer arithmetic once
from the adopted initial return role; phase changes are only pure frames. -/
theorem from_initial {limits before argument length}
    (input : OrdinaryInput options limits inputRemaining span before argument length place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (enabled : machine.borrowTracker=some tracker) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (absent : machine.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=none)
    (descriptor : machine.memory.findGlobal? input.returnFamily.allocation=before.memory.findGlobal? input.returnFamily.allocation)
    (functions : machine.memory.hasFunctionPointer input.returnFamily.allocation=before.memory.hasFunctionPointer input.returnFamily.allocation)
    (vaLists : machine.memory.hasVaListId input.returnFamily.allocation=before.memory.hasVaListId input.returnFamily.allocation)
    (bases : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==input.returnFamily.allocation)=
      before.user.addresses.baseAddr.find? (fun row=>row.allocId==input.returnFamily.allocation))
    (roots : tracker.global.rootTag? input.returnFamily.allocation=input.tracker.global.rootTag? input.returnFamily.allocation)
    (rootBelow : ∀root,input.tracker.global.rootTag? input.returnFamily.allocation=some root→root.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (protectors : ∀row∈tracker.global.protectedTags.entries,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (registry : machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==input.returnFamily.allocation)=false)
    (race : machine.dataRace=none) (ghost : machine.user.payload.ghost=false)
    (backend : machine.user.payload.payload.user.backend=.none) :
    ∃D : CurrentData machine tracker frames frame borrowFrame place,
      D.family=input.returnFamily ∧D.offset=input.returnOffset ∧CurrentPayload before input.returnFamily.allocation D.source := by
  obtain ⟨_,noFunction,noVaList,_,⟨root,concrete,rootCached⟩,source,current,size,_,physical⟩:=latent
  obtain ⟨base,cached,room,address,nonnull,_⟩:=input.returnRepresentation
  have extent : source.len=input.returnCapacity.toNat:=by rw [physical.1.1,size];rfl
  have offsetBound : input.returnOffset.toNat+1≤input.returnCapacity.toNat:=by
    simpa only [size,Size.ofBytes,UInt64.toNat_one] using physical.2.2.1
  have sumBound : base.toNat+input.returnOffset.toNat<2^64:=by omega
  have bits : input.returnFamily.value.offset.bytes=base+input.returnOffset:=by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumBound]
    exact address
  have value : input.returnFamily.value=Pointer.new (.concrete input.returnFamily.allocation root) (Size.ofBytes (base+input.returnOffset)):=by
    cases equal : input.returnFamily.value with
    | mk position provenance=>
      simp only [equal] at concrete bits
      cases position
      simp only [Pointer.new,Size.ofBytes]
      simp_all
  have currentNext : CurrentPayload machine input.returnFamily.allocation source:=by
    cases current with
    | memory actual=>exact .memory (descriptor.trans actual)
    | internalStatic definition actual initializer=>exact .internalStatic definition (descriptor.trans actual) initializer
  let D : CurrentData machine tracker frames frame borrowFrame place:={
    enabled:=enabled,frameBorrow:=frameBorrow,fresh:=fresh,family:=input.returnFamily,root:=root,source:=source,
    base:=base,offset:=input.returnOffset,value:=value,physicalPointer:=input.returnEncoding,layout:=input.returnLayout,
    aligned:=input.returnAligned,physical:=physical,current:=currentNext,absent:=absent,
    noFunction:=functions.trans noFunction,noVaList:=vaLists.trans noVaList,cached:=bases.trans cached,
    rootCached:=roots.trans rootCached,addressRoom:=by rw [extent];exact room,
    nonnull:=by rw [←bits];exact nonnull,rootBelow:=rootBelow root rootCached,protectors:=protectors,
    registry:=registry,race:=race,ghost:=ghost,backend:=backend}
  exact ⟨D,rfl,rfl,current⟩

/-- Genuine current LIVE Bool resources, supplied by the shared live transport
or the SAME-ID actual source materialization packet. -/
structure LiveData (machine : Before) (tracker : MachineHooks.BorrowState)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (place : MPlaceTy Provenance) where
  data : Identities
  owner : Nat
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place
  window : UniformWindow machine tracker data owner physical.id physical.offset.toNat 1 .ret
  enabled : machine.borrowTracker=some tracker
  frameBorrow : frame.extra.borrowTracker=some borrowFrame
  pointer : physical.pointer=window.pointer.value
  allocation : physical.entry.allocation=window.allocation
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global
  binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1
  distinct : window.allocation.extra.roots.toList.Nodup
  fresh : tracker.global.nextPointerTag.value<18446744073709551615
  short : window.allocation.extra.nodes.size+1<65536
  ghost : machine.user.payload.ghost=false
  race : machine.dataRace=none
  backend : machine.user.payload.payload.user.backend=.none
  ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1

structure LiveProtected (D : LiveData machine tracker frame borrowFrame place)
    (frames : Array CompilerFrameContext.ActualFrame) where
  operation : GeneralBorrowForestFnEntry.Output
  post : RootState
  output : CurrentCallPostEntryCheckpoint.Return post.machine ⟨operation.global,tracker.retagMode⟩ place
  actual : (ExecutionMachine.callHooks (config options remaining span) options.limits).protectArgument () place
    (Storage.withCurrent frames frame machine)=.ok () post
  id : output.id=D.physical.id
  offset : output.offset=D.physical.offset.toNat
  original : output.original=D.window.pointer
  tag : output.node.tag=tracker.global.nextPointerTag
  nodes : output.window.allocation.extra.nodes.size≤D.window.allocation.extra.nodes.size+1
  tracked : post.machine.borrowTracker=some ⟨operation.global,tracker.retagMode⟩
  global : operation.global=(GeneralBorrowFnEntryRegistration.registered tracker.global borrowFrame D.physical.id D.fresh).1
  stack : post.stack=(Storage.withCurrent frames
    (registeredFrame frame borrowFrame D.physical.id tracker.global.nextPointerTag) machine).stack
  raw : CandidateCurrentFnEntryRaw.operation D.window.allocation.extra tracker.global borrowFrame D.physical.id
    D.window.pointer.value.provenance D.physical.offset 1=.ok operation
  machineEq : post.machine={(ReturnProtection.borrowedState frames frame borrowFrame machine tracker D.fresh
      D.physical.id D.physical.entry operation.child.tree).machine with memory:=
    {(ReturnProtection.borrowedState frames frame borrowFrame machine tracker D.fresh D.physical.id D.physical.entry operation.child.tree).machine.memory with
      live:=(((ReturnProtection.borrowedState frames frame borrowFrame machine tracker D.fresh D.physical.id D.physical.entry operation.child.tree).machine.memory.live.filter
        (fun row=>row.1!=D.physical.id)).push (D.physical.id,{D.physical.entry with allocation:=output.window.allocation}))}}

  tagMapping : output.window.allocation.extra.tagMapping=operation.child.tree.tagMapping
  extra : output.window.allocation.extra=(operation.child.tree.performBorrowAccessRange (.concrete operation.tag)
    (Size.ofBytes D.physical.offset) (Size.ofBytes 1) .Write operation.global.protectedTags .VisitChildrenOfAccessed).tree
  write : Allocation.writeUninit (allocRange (Size.ofBytes D.physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
    ((D.physical.entry.allocation.setExtra operation.child.tree).setExtra
      (operation.child.tree.performBorrowAccessRange (.concrete operation.tag) (Size.ofBytes D.physical.offset) (Size.ofBytes 1)
        .Write operation.global.protectedTags .VisitChildrenOfAccessed).tree)=.ok () output.window.allocation

theorem live (ctx : ActualRetagContext.Context options remaining span)
    (D : LiveData machine tracker frame borrowFrame place) (frames : Array CompilerFrameContext.ActualFrame) :
    Nonempty (LiveProtected (options:=options) (remaining:=remaining) (span:=span) D frames) := by
  obtain ⟨operation,post,R,actual,id,offset,original,tag,nodes,tracked,global,stack,raw,tagMapping,extra,write,machineEq⟩:=
    CurrentCallConversionBool.protect_live options remaining span ctx machine tracker D.data D.owner frames frame borrowFrame
      D.enabled D.frameBorrow place D.physical D.window D.pointer D.allocation D.runtime D.binding D.distinct D.fresh D.short
      D.ghost D.race D.backend D.ready
  exact ⟨⟨operation,post,R,actual,id,offset,original,tag,nodes,tracked,global,stack,raw,machineEq,tagMapping,extra,write⟩⟩

structure FirstProtected {limits before argument length}
    {input : OrdinaryInput options limits inputRemaining span before argument length place}
    (D : CurrentData machine tracker frames frame borrowFrame place) (phase : FirstPhase input D) where
  externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance)
  wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
    PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic
  finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState
  finalTape : ExecutionChoices.Tape
  result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
    (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
    (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve finalAddresses finalTape
  protection : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic
    (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve finalAddresses finalTape result

structure NextProtected {limits before argument length}
    {input : OrdinaryInput options limits inputRemaining span before argument length place}
    (D : CurrentData machine tracker frames frame borrowFrame place) (phase : NextPhase input D) where
  result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
    (CurrentCallConversionActualEnsure.hooks options).address phase.externStatic D.registered.machine D.next
    (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve phase.finalAddresses phase.finalTape
  protection : Protected (options:=options) (remaining:=remaining) (span:=span) D phase.externStatic
    (phase.rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) phase.reserve phase.finalAddresses phase.finalTape result

/-- Internal resource classification of the actual post-source Bool lookup.
The LIVE alternative carries its actual row; both CURRENT alternatives carry
actual absence. SAME-ID materialization therefore uses only the LIVE branch. -/
inductive Branch {limits before argument length}
    (input : OrdinaryInput options limits inputRemaining span before argument length place)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) where
  | live (data : LiveData machine tracker frame borrowFrame place)
  | first (data : CurrentData machine tracker frames frame borrowFrame place) (phase : FirstPhase input data)
  | next (data : CurrentData machine tracker frames frame borrowFrame place) (phase : NextPhase input data)

def Output {limits before argument length}
    {input : OrdinaryInput options limits inputRemaining span before argument length place}
    (branch : Branch input machine tracker frames frame borrowFrame) : Type :=
  match branch with
  | .live data=>LiveProtected (options:=options) (remaining:=remaining) (span:=span) data frames
  | .first data phase=>FirstProtected (remaining:=remaining) data phase
  | .next data phase=>NextProtected (remaining:=remaining) data phase

/-- ONE shared Bool dispatcher. Every operation equation and converter result
is produced internally from current resources and initial selected data. -/
theorem invoke {limits before argument length}
    {input : OrdinaryInput options limits inputRemaining span before argument length place}
    (ctx : ActualRetagContext.Context options remaining span)
    (branch : Branch input machine tracker frames frame borrowFrame) : Nonempty (Output (remaining:=remaining) branch) := by
  cases branch with
  | live data=>exact live ctx data frames
  | first data phase=>
    obtain ⟨externStatic,wiring,finalAddresses,finalTape,result,⟨protection⟩⟩:=first input ctx data phase
    exact ⟨⟨externStatic,wiring,finalAddresses,finalTape,result,protection⟩⟩
  | next data phase=>
    obtain ⟨result,⟨protection⟩⟩:=next input ctx data phase
    exact ⟨⟨result,protection⟩⟩

end
end DuplicatePrefix.CurrentCallConversionBoolPhase
