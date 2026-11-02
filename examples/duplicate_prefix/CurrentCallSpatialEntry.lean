import duplicate_prefix.CurrentCallSpatialBoolActivation
import duplicate_prefix.CurrentCallSpatialEntryControl
import duplicate_prefix.CurrentCallBoolTreeWindow
import duplicate_prefix.CurrentCallPreparedResources
import duplicate_prefix.CurrentCallResourcePreparedEntry
import duplicate_prefix.CurrentCallSpatialFamilyFormation

namespace DuplicatePrefix.CurrentCallSpatialEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialSourceInstall
open GeneralBorrowFnEntryRegistration CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallTypedSourceCopy
open CurrentCallSpatialJointInstall
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Initial selected-role resources and execution representation. There are no
operation outcomes, future machines, or whole-source completion witnesses. -/
structure Conditions (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame) (before : Before) (tracker : MachineHooks.BorrowState)
    (ctx : CurrentCallSpatialCover.Context before) (offset : Nat) (len : UInt64)
    (source : RoleCover before tracker ctx .mut offset len.toNat) (returnOffset : Nat)
    (ret : RoleCover before tracker ctx .ret returnOffset 1) (place : MPlaceTy Provenance) where
  model : DuplicatePrefixCallModel.Model options remaining span before
  state : DuplicatePrefixRuntimeInput.State before tracker
  highwater : ∀row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag
  rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout)
  borrowFrame : FrameState
  frameBorrow : root.frame.extra.borrowTracker=some borrowFrame
  binding : CandidateCallBindings.WindowBinding before source.family.value source.backing.id offset len.toNat
  positive : 0<len.toNat
  signedFits : len.toNat<9223372036854775808
  tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615
  sourceRoom : source.backing.allocation.extra.nodes.size+2<65536
  boolRoom : ret.backing.allocation.extra.nodes.size+2<65536
  dynamicFuel : Nat
  validationFuel : Nat
  dynamicEq : options.place.dynamicFuel=dynamicFuel+1
  validationEq : options.limits.validation=validationFuel+1
  origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place
  physicalId : physical.id=ret.backing.id
  physicalOffset : physical.offset.toNat=returnOffset
  returnPointer : physical.pointer=ret.family.value
  returnBinding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1
  ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1
  separate : ∀byte,Window source.backing.id offset len.toNat byte→Window ret.backing.id returnOffset 1 byte→False

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    (C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place)

include C in
theorem Conditions.fresh : tracker.global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  change tracker.global.nextPointerTag.value.toNat<18446744073709551615
  have h:=C.tagRoom
  omega

def sourceOutput := CurrentCallSpatialEntryRead.output source C.borrowFrame
  C.fresh (UInt64.ofNat offset) len

def argsRoot (count : UInt64) : RootFrame := RootArgumentsTwo.result
  (CurrentCallSourceArguments.doneRoot options remaining span root C.borrowFrame source.family.value len source.backing.id tracker.global.nextPointerTag) count

def finalMachine (place : MPlaceTy Provenance) (machine : Before) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (retagged : RootState) (updated : Allocation Provenance BorrowTree) : Before :=
  {retagged.machine with memory:={retagged.machine.memory with live:=
    ((retagged.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}

def protectedState (count : UInt64) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow (copiedMachine source C.borrowFrame
      C.fresh (UInt64.ofNat offset) len entry) place)
    (fresh : (sourceOutput C).global.nextPointerTag.value<18446744073709551615)
    (boolOutput : GeneralBorrowForestFnEntry.Output) : RootState := borrowedState frames (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame
    (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len entry)
    ⟨(sourceOutput C).global,tracker.retagMode⟩ fresh physical.id physical.entry boolOutput.child.tree

structure Output (limits : ExecutionMachine.Limits) (count : UInt64) where
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  sourceLive : before.memory.live.find? (fun row=>row.1==source.backing.id)=some (source.backing.id,entry)
  allocation : entry.allocation=source.backing.allocation
  child : UniIndex
  sourceActual : CandidateCurrentFnEntryRaw.operation entry.allocation.extra tracker.global C.borrowFrame source.backing.id
    source.family.value.provenance (UInt64.ofNat offset) len=.ok (sourceOutput C)
  sourceLookup : (sourceOutput C).child.tree.indexOfTag (sourceOutput C).tag=some child
  sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (sourceOutput C).child.tree (sourceOutput C).global
  sourceGrowth : (sourceOutput C).child.tree.nodes.size≤source.backing.allocation.extra.nodes.size+1
  models : ∀i,ParentInterpretation (sourceOutput C).child.tree (CurrentCallSpatialJointInstall.extended source C.positive child i)
  sourceTracked : DuplicatePrefixRuntimeInput.State (copiedMachine source C.borrowFrame
    C.fresh (UInt64.ofNat offset) len entry) ⟨(sourceOutput C).global,tracker.retagMode⟩
  src : RoleCover (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len entry)
    ⟨(sourceOutput C).global,tracker.retagMode⟩
    (CurrentCallSpatialJointInstall.context source C.positive C.borrowFrame C.fresh
      (UInt64.ofNat offset) len entry allocation child models) .mut offset len.toNat
  dst : RoleCover (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len entry)
    ⟨(sourceOutput C).global,tracker.retagMode⟩
    (CurrentCallSpatialJointInstall.context source C.positive C.borrowFrame C.fresh
      (UInt64.ofNat offset) len entry allocation child models) .ret returnOffset 1
  sourceFamily : src.family=childFamily source (sourceOutput C).tag
  returnFamily : dst.family=ret.family
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow
    (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len entry) place
  physicalId : physical.id=dst.backing.id
  physicalOffset : physical.offset.toNat=returnOffset
  physicalPointer : physical.pointer=dst.family.value
  fresh : (sourceOutput C).global.nextPointerTag.value<18446744073709551615
  boolOutput : GeneralBorrowForestFnEntry.Output
  boolChild : UniIndex
  boolActual : CandidateCurrentFnEntryRaw.operation
    (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset).allocation.extra
    (sourceOutput C).global (sourceOutput C).frame physical.id
    (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset).pointer.value.provenance physical.offset 1=.ok boolOutput
  boolTag : boolOutput.tag=(sourceOutput C).global.nextPointerTag
  boolGlobal : boolOutput.global=(registered (sourceOutput C).global (sourceOutput C).frame physical.id fresh).1
  boolFrame : boolOutput.frame=(registered (sourceOutput C).global (sourceOutput C).frame physical.id fresh).2
  boolWitness : Nonempty (CurrentCallResourceFnEntry.BorrowWitness
    (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset) boolOutput boolChild physical.offset 1)
  updated : Allocation Provenance BorrowTree
  updatedExtra : updated.extra=(boolOutput.child.tree.performBorrowAccessRange (.concrete (sourceOutput C).global.nextPointerTag)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write boolOutput.global.protectedTags .VisitChildrenOfAccessed).tree
  updatedSize : updated.byteSize=physical.entry.allocation.byteSize
  updatedLength : updated.len=physical.entry.allocation.len
  updatedMutable : updated.mutability=.Mut
  updatedSnapshot : AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation
  updatedRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra boolOutput.global
  updatedParents : ParentInterpretation updated.extra (S05ConcreteProtectedChildCompletion.extend
    (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset).precise.completion boolChild
    (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset).pointer.grant)
  updatedOwned : GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority updated.extra
    (S05ConcreteProtectedChildCompletion.extend (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset).precise.completion boolChild
      (CurrentCallSpatialBoolActivation.window dst physical physicalId physicalOffset).pointer.grant) boolOutput.global.protectedTags boolChild)
    physical.offset (physical.offset+1) updated.extra.locations
  arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      ⟨.immediate (value options remaining span source.family.value len).imm,ActualReferenceMetadata.reference⟩ (second count))
    (Storage.withCurrent frames root.frame before)=.ok (2,2)
      (Storage.withCurrent frames (argsRoot C count).frame (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len entry))
  actual : CurrentCallSpatialEntryControl.action (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
    (value options remaining span source.family.value len).imm count place (Storage.withCurrent frames root.frame before)=
    .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
      {registeredFrame (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame physical.id (sourceOutput C).global.nextPointerTag
        with location:=.unwinding ⟨559⟩}) (finalMachine place _ physical (protectedState C count entry physical fresh boolOutput) updated))
  tail : RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
    (Storage.withCurrent frames (argsRoot C count).frame (copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len entry))=
    .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
      {registeredFrame (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame physical.id (sourceOutput C).global.nextPointerTag
        with location:=.unwinding ⟨559⟩}) (finalMachine place _ physical (protectedState C count entry physical fresh boolOutput) updated))
  sourceFrames : ∀(i : Fin src.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active src i)
    (byte : AllocId×Nat) (request : Window src.backing.id offset len.toNat byte)
    (cell : Window src.backing.id src.backing.cells[i].offset src.backing.cells[i].length byte),
    ∃(data : Identities) (Q : UniformWindow (finalMachine place _ physical (protectedState C count entry physical fresh boolOutput) updated)
      ⟨boolOutput.global,tracker.retagMode⟩ data 0 src.backing.id byte.2 1 .ret),
      Q.allocation=(if src.backing.id=dst.backing.id then updated else src.backing.allocation) ∧
      Q.pointer=src.family.at (src.roles i overlap).grant ∧
      Q.precise.completion=(if src.backing.id=dst.backing.id then
        S05ConcreteProtectedChildCompletion.extend src.backing.cells[i].completion boolChild (dst.roles (CurrentCallSpatialReturnFrame.returnIndex dst) (CurrentCallSpatialReturnFrame.returnOverlap dst)).grant
        else src.backing.cells[i].completion)

private theorem runtime_present {before : Before} {tracker : MachineHooks.BorrowState}
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree) (present : Present (ActualWorld before) id allocation) :
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global := by
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨row,member,same⟩ := List.mem_map.mp present
  have selected : DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global :=
    ⟨state.formed row member,state.coherent row member,state.possible row member,highwater row member⟩
  have allocationEq := (Prod.mk.inj same).2
  rw [allocationEq] at selected
  exact selected


/-- Both selected roles drive the actual source-copy/Bool-protection sequence.
The output's pointwise certificates use one deterministic source-stage context. -/
theorem body (limits : ExecutionMachine.Limits) (count : UInt64) : Nonempty (Output C limits count) := by
  let role := source
  let cover := ctx
  have contexts := DuplicatePrefixCallModel.contexts options remaining span before C.model
  obtain ⟨refCtx⟩ := contexts.1
  obtain ⟨retagCtx⟩ := contexts.2.2.2
  let ctx := refCtx
  let state := C.state
  let highwater := C.highwater
  have runtime := runtime_present state highwater role.backing.id role.backing.allocation role.backing.live
  have distinct : role.backing.allocation.extra.roots.toList.Nodup := by
    have present := role.backing.live
    simp only [Present,ActualWorld,Array.toList_map] at present
    obtain ⟨⟨id,entry⟩,member,equal⟩ := List.mem_map.mp present
    rcases Prod.mk.inj equal with ⟨rfl,equal⟩
    simpa only [←equal] using state.roots (role.backing.id,entry) member
  have short : role.backing.allocation.extra.nodes.size<65536 := by change source.backing.allocation.extra.nodes.size<65536;have h:=C.sourceRoom;omega
  have nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295 := by change source.backing.allocation.extra.nodes.size+1≤4294967295;have h:=C.sourceRoom;omega
  let prepared := firstLive root
  let frame := prepared.frame
  let borrowFrame := C.borrowFrame
  have frameBorrow : frame.extra.borrowTracker=some borrowFrame := C.frameBorrow
  let binding := C.binding
  let positive := C.positive
  let signedFits := C.signedFits
  let room := C.fresh
  let race := C.model.noDataRace
  let nullComparator := C.model.nullComparator
  let dynamicFuel := C.dynamicFuel
  let validationFuel := C.validationFuel
  let fuelEq := C.dynamicEq
  let validationEq := C.validationEq
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime := C.model.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)) := C.origins
  let debugOff := C.model.debugOff
  let ghostOff := C.model.ghostOff
  let shallowMode := C.model.shallow
  let localId : MIR.LocalId := 1
  let valid : localId<frame.locals.size := prepared.valid i1
  let old : Immediate Provenance := .uninit
  have live : frame.locals[localId].value=.live (.immediate old) := by
    simp only [frame,prepared,localId,old,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference := by
    simp only [frame,prepared,localId,firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  have noClocks : frame.extra.dataRace=none := prepared.noClocks
  let separate := C.separate
  obtain ⟨entry,doneFrame,child,installed,sourceLive,allocation,copyStep,lookup,borrowed,returnPlace,continuation,body,bodyIdentity,functionInstance,location,postState,postHighwater,_⟩ :=
    CurrentCallSpatialSourceState.invoke options limits remaining span ctx before tracker cover offset len role runtime state highwater distinct short nodeRoom frames frame borrowFrame frameBorrow binding positive signedFits room race nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  obtain ⟨physicalEntry,base,physicalLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have sameEntry : physicalEntry=entry := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans sourceLive))).2
  subst physicalEntry
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have treeLength := state.treeLength (role.backing.id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive))
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,←allocation,treeLength,←length]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;cases positive
  have joined : ∃(q : UniIndex) (models : ∀i,ParentInterpretation (CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).child.tree (extended role positive q i)),
      (CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).child.tree.indexOfTag tracker.global.nextPointerTag=some q ∧
      ∃(src : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨(CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).global,tracker.retagMode⟩
          (context role positive borrowFrame room (UInt64.ofNat offset) len entry allocation q models) .mut offset len.toNat)
        (dst : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨(CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).global,tracker.retagMode⟩
          (context role positive borrowFrame room (UInt64.ofNat offset) len entry allocation q models) .ret returnOffset 1),
        src.family=childFamily role tracker.global.nextPointerTag ∧dst.family=ret.family := by
    by_cases same : ret.backing.id=role.backing.id
    · exact same_views role ret same (by intro byte sourceHit retHit;apply separate byte sourceHit;simpa only [same] using retHit)
        runtime distinct short nodeRoom borrowFrame room (UInt64.ofNat offset) len startEq rfl nonzero bounds positive entry allocation postState
    · exact different_views role ret same (runtime_present state highwater ret.backing.id ret.backing.allocation ret.backing.live)
        runtime distinct short nodeRoom borrowFrame room (UInt64.ofNat offset) len startEq rfl nonzero bounds positive entry allocation postState
  obtain ⟨q,models,qLookup,src,dst,sourceFamily,retFamily⟩ := joined
  have same : q=child := Option.some.inj (qLookup.symm.trans lookup)
  subst q
  obtain ⟨copyEntry,copyChild,copyLive,copyAllocation,sourceActual,sourceTag,sourceGlobal,sourceFrame,copyLookup,readDone,childDone,afterRuntime,capacity,growth,oldRoots,oldFields,newNode,typed,copied,_⟩ :=
    CurrentCallSpatialTypedSourceCopy.invoke options limits remaining span ctx before tracker cover offset len role runtime
      (by simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds)
      distinct short nodeRoom frames frame borrowFrame state.enabled frameBorrow C.binding positive signedFits room race
      nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  have sameEntry : copyEntry=entry := (Prod.mk.inj (Option.some.inj (copyLive.symm.trans sourceLive))).2
  subst copyEntry
  obtain ⟨checked,copy,_,sourceTracked,sourceInstalled,frameSource,sourceSize,sourceValue,sourceGhost,types,addresses,threads,dataRace⟩ := copied
  let sourceAfter := CurrentCallTypedSourceCopy.validated before tracker room role.backing.id entry (sourceOutput C).child.tree
  let sourceMachine := copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry
  let nextFn : MachineHooks.BorrowState := ⟨(sourceOutput C).global,.FnEntry⟩
  have sourceAfterTracked : sourceAfter.borrowTracker=some nextFn := sourceTracked
  have arguments := (CurrentCallSourceArguments.arguments options limits remaining span debugOff validationFuel validationEq
    frames root C.rawLocals before sourceAfter tracker nextFn state.enabled sourceAfterTracked ghostOff shallowMode
    sourceGhost shallowMode borrowFrame role.family.value len count role.backing.id tracker.global.nextPointerTag copy).2
  have memory : sourceMachine.memory.live=(before.memory.live.filter (fun row=>row.1!=role.backing.id)).push
      (role.backing.id,{entry with allocation:=entry.allocation.setExtra (sourceOutput C).child.tree}) := rfl
  obtain ⟨physical,physicalPointer,physicalId,physicalOffset,_,physicalBinding⟩ := CurrentCallBoolTreeWindow.replace
    (final:=sourceMachine) C.physical C.returnBinding role.backing.id entry sourceLive (sourceOutput C).child.tree addresses memory
  have dstId : dst.backing.id=ret.backing.id := dst.id.symm.trans ((congrArg Family.allocation retFamily).trans ret.id)
  have physicalDst : physical.id=dst.backing.id := physicalId.trans (C.physicalId.trans dstId.symm)
  have physicalNat : physical.offset.toNat=returnOffset := (congrArg UInt64.toNat physicalOffset).trans C.physicalOffset
  have physicalValue : physical.pointer=dst.family.value := physicalPointer.trans (C.returnPointer.trans (congrArg Family.value retFamily).symm)
  have retAlloc : C.physical.entry.allocation=ret.backing.allocation := by
    apply CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList
      (by simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds) C.physical.id
    · simp only [Present,ActualWorld,Array.toList_map]
      exact List.mem_map.mpr ⟨(C.physical.id,C.physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some C.physical.live),rfl⟩
    · rw [C.physicalId];exact ret.backing.live
  have boolShort : physical.entry.allocation.extra.nodes.size+1<65536 := by
    by_cases same : role.backing.id=C.physical.id
    · have entryEq : entry=C.physical.entry := (Prod.mk.inj (Option.some.inj ((same ▸ sourceLive).symm.trans C.physical.live))).2
      have freshLive : sourceMachine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{entry with allocation:=entry.allocation.setExtra (sourceOutput C).child.tree}) := by
        rw [physicalId,←same,memory]
        exact MemoryCopyBridge.live_lookup_replaced before.memory role.backing.id _
      have physicalEntry : physical.entry={entry with allocation:=entry.allocation.setExtra (sourceOutput C).child.tree} :=
        (Prod.mk.inj (Option.some.inj (physical.live.symm.trans freshLive))).2
      rw [physicalEntry]
      have roomB:=C.boolRoom
      rw [←retAlloc,←entryEq,allocation] at roomB
      change (sourceOutput C).child.tree.nodes.size+1<65536
      have growth' : (sourceOutput C).child.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 := growth
      omega
    · have freshLive : sourceMachine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,C.physical.entry) := by
        rw [physicalId,memory,Array.find?_push,Array.find?_filter]
        have pred : (fun row : AllocId×LocalAllocation Provenance BorrowTree MiriMemoryKind=>decide ((row.1!=role.backing.id)=true ∧(row.1==C.physical.id)=true))=(fun row=>row.1==C.physical.id) := by
          funext row
          by_cases hit : row.1=C.physical.id
          · simp [hit,Ne.symm same]
          · simp [hit]
        rw [pred,C.physical.live]
        simp [same]
      have physicalEntry : physical.entry=C.physical.entry := (Prod.mk.inj (Option.some.inj (physical.live.symm.trans freshLive))).2
      rw [physicalEntry,retAlloc]
      have h:=C.boolRoom
      omega
  have returnRoom : (sourceOutput C).global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (sourceOutput C).global.nextPointerTag.value.toNat<18446744073709551615
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    have h:=C.tagRoom
    change (CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).global.nextPointerTag.value.toNat<18446744073709551615
    rw [sourceGlobal]
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat<18446744073709551615
    omega
  have frameBool : (atSpan (argsRoot C count) ⟨601⟩).frame.extra.borrowTracker=some (sourceOutput C).frame := by
    change (atSpan (argsRoot C count) ⟨601⟩).frame.extra.borrowTracker=some (CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len).frame
    rw [sourceFrame]
    exact CurrentCallSourceArguments.result_borrowFrame options remaining span root borrowFrame role.family.value len count role.backing.id tracker.global.nextPointerTag
  have ready : CurrentCallBoolProtection.WindowReady sourceMachine physical.id physical.offset.toNat 1 := by
    rw [physicalId,physicalOffset]
    exact C.ready.transport rfl
  have disjoint : ∀byte,Window src.backing.id offset len.toNat byte→Window dst.backing.id returnOffset 1 byte→False := by
    have sid : src.backing.id=role.backing.id := src.id.symm.trans ((congrArg Family.allocation sourceFamily).trans (by rfl))
    intro byte left right
    exact separate byte (by simpa only [sid] using left) (by simpa only [dstId] using right)
  obtain ⟨boolOutput,boolChild,boolActual,boolTag,boolGlobal,boolFrame,boolWitness,updated,protection,extra,bytes,byteLength,mutable,mutation,snapshot,retaggedTracked,frameTracked,destination,ctorState,writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity,sourceFrames⟩ :=
    CurrentCallSpatialBoolActivation.activate_sources options limits (remaining+1) span retagCtx sourceMachine
      ⟨(sourceOutput C).global,tracker.retagMode⟩ _ returnOffset dst offset len.toNat src disjoint
      frames (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame postState postHighwater frameBool
      place physical physicalDst physicalNat physicalValue physicalBinding returnRoom boolShort
      sourceGhost (dataRace.trans race) C.model.noBackend ready
  have finish := CurrentCallSpatialEntryControl.finish_of_arguments options limits remaining span frames root C.rawLocals
    borrowFrame role.family.value len count role.backing.id tracker.global.nextPointerTag before sourceMachine
    (finalMachine place _ physical (protectedState C count entry physical returnRoom boolOutput) updated)
    (sourceOutput C).frame physical.id (sourceOutput C).global.nextPointerTag place arguments protection
  have actualExtra : updated.extra=(boolOutput.child.tree.performBorrowAccessRange (.concrete (sourceOutput C).global.nextPointerTag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write boolOutput.global.protectedTags .VisitChildrenOfAccessed).tree := by
    rw [boolGlobal]
    exact extra
  exact ⟨⟨entry,sourceLive,allocation,child,sourceActual,lookup,afterRuntime,growth,models,postState,src,dst,sourceFamily,retFamily,physical,physicalDst,physicalNat,physicalValue,
    returnRoom,boolOutput,boolChild,boolActual,boolTag,boolGlobal,boolFrame,boolWitness,updated,actualExtra,bytes,byteLength,mutable,snapshot,
    by rw [extra];exact writeRuntime,by rw [extra];exact writeParents,by rw [extra];exact writeOwned,
    arguments,finish.1,finish.2,sourceFrames⟩⟩

/-- Raw push changes only frame identities and relevance caches. -/
def preparedBacking {before} (backing : AllocationCover before) (frames : Array CompilerFrameContext.ActualFrame) :
    AllocationCover (CurrentCallPush.preparedMachine before frames) :=
  ⟨backing.id,backing.allocation,backing.live,backing.cells,backing.disjoint⟩

def preparedContext {before} (ctx : CurrentCallSpatialCover.Context before) (frames : Array CompilerFrameContext.ActualFrame) :
    CurrentCallSpatialCover.Context (CurrentCallPush.preparedMachine before frames) where
  allocations := ctx.allocations.map (fun a=>preparedBacking a frames)
  unique := by simpa only [Array.toList_map,List.map_map,Function.comp_def,preparedBacking] using ctx.unique

def preparedRole {before tracker ctx mode offset length} (role : RoleCover before tracker ctx mode offset length)
    (frames : Array CompilerFrameContext.ActualFrame) :
    RoleCover (CurrentCallPush.preparedMachine before frames) tracker (preparedContext ctx frames) mode offset length where
  family := role.family
  backing := preparedBacking role.backing frames
  backingAt := by
    change preparedBacking role.backing frames∈(ctx.allocations.map (fun a=>preparedBacking a frames)).toList
    rw [Array.toList_map]
    exact List.mem_map.mpr ⟨role.backing,role.backingAt,rfl⟩
  id := role.id
  covered := role.covered
  roles := fun i overlap=>⟨(role.roles i overlap).grant,(role.roles i overlap).binding,
    CurrentCallPreparedResources.issued (role.roles i overlap).issued frames,(role.roles i overlap).available⟩

def prepared : Conditions options remaining span frames root (CurrentCallPush.preparedMachine before frames) tracker
    (preparedContext ctx frames) offset len (preparedRole source frames) returnOffset (preparedRole ret frames) place where
  model := CurrentCallResourcePreparedEntry.model C.model frames
  state := CurrentCallPreparedResources.state C.state frames
  highwater := CurrentCallPreparedResources.highwater C.highwater frames
  rawLocals := C.rawLocals
  borrowFrame := C.borrowFrame
  frameBorrow := C.frameBorrow
  binding := CurrentCallPreparedResources.windowBinding C.binding frames
  positive := C.positive
  signedFits := C.signedFits
  tagRoom := C.tagRoom
  sourceRoom := C.sourceRoom
  boolRoom := C.boolRoom
  dynamicFuel := C.dynamicFuel
  validationFuel := C.validationFuel
  dynamicEq := C.dynamicEq
  validationEq := C.validationEq
  origins := C.origins
  physical := CurrentCallResourcePreparedEntry.physical C.physical frames
  physicalId := C.physicalId
  physicalOffset := C.physicalOffset
  returnPointer := C.returnPointer
  returnBinding := CurrentCallPreparedResources.windowBinding C.returnBinding frames
  ready := C.ready.transport rfl
  separate := C.separate

/-- The paired LIVE spatial resources derive every source and Bool operation
inside the actual root initialization. No operation result or future resource
state is a premise. This is not ordinary-input coverage. -/
theorem invoke {options remaining span frames before tracker ctx offset len source returnOffset ret place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span frames (CurrentCallSpatialEntryControl.root before frames place race)
      before tracker ctx offset len source returnOffset ret place)
    (stackReady : CurrentCallPush.StackReadiness before frames) (count : UInt64) :
    ∃out : Output (prepared C) limits count,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (value options remaining span source.family.value len).imm,ActualReferenceMetadata.reference⟩,
          .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
          {registeredFrame (atSpan (argsRoot (prepared C) count) ⟨601⟩).frame (sourceOutput (prepared C)).frame out.physical.id
            (sourceOutput (prepared C)).global.nextPointerTag with location:=.unwinding ⟨559⟩})
          (finalMachine place _ out.physical (protectedState (prepared C) count out.entry out.physical out.fresh out.boolOutput) out.updated)) := by
  obtain ⟨out⟩ := body (prepared C) limits count
  refine ⟨out,?_⟩
  exact CurrentCallSpatialEntryControl.init_of_steps options limits remaining span before frames place race C.model.debugOff
    stackReady (value options remaining span source.family.value len).imm count _
    (argsRoot (prepared C) count) _ out.arguments out.tail

open CurrentCallFamilySatisfaction
variable {C}

def Output.sourceAssignment {limits count actual} (out : Output C limits count) (a : Assignment actual) :=
  CurrentCallSpatialFamilyFormation.append a out.src

def Output.boolPayload {limits count} (out : Output C limits count) : Payload :=
  ⟨out.physical.id,(CurrentCallResourceFnEntry.child_pointer
    (CurrentCallSpatialBoolActivation.window out.dst out.physical out.physicalId out.physicalOffset)
      out.boolOutput.tag out.boolChild).value⟩

def Output.assignment {limits count actual} (out : Output C limits count) (a : Assignment actual) :=
  (out.sourceAssignment a).retag out.boolPayload out.boolPayload.value.withOptionalProvenance
    (by simp [Represents,Pointer.withOptionalProvenance])

/-- The two ACTUAL creator outputs obtain two appended semantic IDs. The
original destination occurrence/family remains exact; re-slotting grants no
new rights and changes no per-cell witness. -/
theorem Output.formed {limits count actual occurrence oldFamily} (out : Output C limits count) (a : Assignment actual)
    (originalReturn : a.Binds occurrence oldFamily) :
    (out.assignment a).Binds actual.size (CurrentCallSpatialFamilyFormation.role a out.src).family ∧
    (out.assignment a).Binds (actual.size+1) ((out.sourceAssignment a).newFamily out.boolPayload) ∧
    (out.assignment a).Binds occurrence oldFamily ∧
    (CurrentCallSpatialFamilyFormation.role a out.src).family.slot=a.families.size ∧
    ((out.sourceAssignment a).newFamily out.boolPayload).slot=a.families.size+1 ∧
    (CurrentCallSpatialFamilyFormation.role a out.src).family.slot≠((out.sourceAssignment a).newFamily out.boolPayload).slot ∧
    (∀grant,(CurrentCallSpatialFamilyFormation.role a out.src).family.at grant=out.src.family.at grant) ∧
    (∀i overlap,((CurrentCallSpatialFamilyFormation.role a out.src).roles i overlap).grant=(out.src.roles i overlap).grant) ∧
    PointerBinds ((CurrentCallSpatialBoolActivation.window out.dst out.physical out.physicalId out.physicalOffset).allocation.setExtra out.boolOutput.child.tree)
      (CurrentCallResourceFnEntry.child_pointer (CurrentCallSpatialBoolActivation.window out.dst out.physical out.physicalId out.physicalOffset)
        out.boolOutput.tag out.boolChild) := by
  have q := CurrentCallSpatialFamilyFormation.formed a out.src
  have qReturn := CurrentCallSpatialFamilyFormation.old_binding a out.src originalReturn
  obtain ⟨witness⟩ := out.boolWitness
  refine ⟨(out.sourceAssignment a).old_reference_after_retag _ _ _ q.1,?_,
    (out.sourceAssignment a).old_reference_after_retag _ _ _ qReturn,rfl,?_,?_,q.2.2.2.2.1,q.2.2.2.2.2,witness.binding⟩
  · simpa only [Output.assignment,Array.size_push] using (out.sourceAssignment a).retagged_family out.boolPayload out.boolPayload.value.withOptionalProvenance
      (show Represents out.boolPayload.value.withOptionalProvenance out.boolPayload.value by simp [Represents,Pointer.withOptionalProvenance])
  · exact Array.size_push _
  · change a.families.size≠(a.families.push _).size
    rw [Array.size_push]
    omega

/-- Protection discards its temporary child pointer. The actual final frame
keeps the ORIGINAL return destination for the later post-pop store. -/
theorem Output.original_returnPlace {limits count} (out : Output C limits count) :
    (CallEntryFacts.doneRootFrame
      {registeredFrame (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame out.physical.id
        (sourceOutput C).global.nextPointerTag with location:=.unwinding ⟨559⟩}).returnPlace=root.frame.returnPlace := by
  change (argsRoot C count).frame.returnPlace=root.frame.returnPlace
  exact CurrentCallSourceArguments.result_returnPlace options remaining span root C.borrowFrame source.family.value len count
    source.backing.id tracker.global.nextPointerTag

/-- The actual paired entry also records fresh nominal q/B identities and
preserves both original ABI family references. These table laws do not infer
identity from equal pointer bits or create additional permissions. -/
theorem invoke_formed {options remaining span frames before tracker ctx offset len source returnOffset ret place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span frames (CurrentCallSpatialEntryControl.root before frames place race)
      before tracker ctx offset len source returnOffset ret place)
    (actual : Array (Pointer (Option Provenance))) (a : CurrentCallFamilySatisfaction.Assignment actual)
    (sourceOccurrence returnOccurrence : Nat)
    (sourceBound : a.Binds sourceOccurrence source.family) (returnBound : a.Binds returnOccurrence ret.family)
    (stackReady : CurrentCallPush.StackReadiness before frames) (count : UInt64) :
    ∃out : Output (prepared C) limits count,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (value options remaining span source.family.value len).imm,ActualReferenceMetadata.reference⟩,
          .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
          {registeredFrame (atSpan (argsRoot (prepared C) count) ⟨601⟩).frame (sourceOutput (prepared C)).frame out.physical.id
            (sourceOutput (prepared C)).global.nextPointerTag with location:=.unwinding ⟨559⟩})
          (finalMachine place _ out.physical (protectedState (prepared C) count out.entry out.physical out.fresh out.boolOutput) out.updated)) ∧
      (out.assignment a).Binds actual.size (CurrentCallSpatialFamilyFormation.role a out.src).family ∧
      (out.assignment a).Binds (actual.size+1) ((out.sourceAssignment a).newFamily out.boolPayload) ∧
      (out.assignment a).Binds sourceOccurrence source.family ∧
      (out.assignment a).Binds returnOccurrence ret.family ∧
      (CurrentCallSpatialFamilyFormation.role a out.src).family.slot=a.families.size ∧
      ((out.sourceAssignment a).newFamily out.boolPayload).slot=a.families.size+1 ∧
      (CurrentCallSpatialFamilyFormation.role a out.src).family.slot≠((out.sourceAssignment a).newFamily out.boolPayload).slot := by
  obtain ⟨out,actualInit⟩ := invoke limits race C stackReady count
  have sourceFormed := out.formed a sourceBound
  have returnFormed := out.formed a returnBound
  exact ⟨out,actualInit,returnFormed.1,returnFormed.2.1,sourceFormed.2.2.1,returnFormed.2.2.1,
    returnFormed.2.2.2.1,returnFormed.2.2.2.2.1,returnFormed.2.2.2.2.2.1⟩

end
end DuplicatePrefix.CurrentCallSpatialEntry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntry.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry dependency {dependency}"
