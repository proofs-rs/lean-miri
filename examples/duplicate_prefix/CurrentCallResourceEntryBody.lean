import duplicate_prefix.CurrentCallResourcePairSource
import duplicate_prefix.CurrentCallSourceArguments
import duplicate_prefix.CurrentCallBoolTreeWindow
import duplicate_prefix.CurrentCallResourceBorrowGrowth

namespace DuplicatePrefix.CurrentCallResourceEntryBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Implementation readiness for the normalized live-source call phase. This
is not ordinary validity: ownership/family admission and materialization into
this phase remain separate. There are no operation outcomes in these fields. -/
structure Conditions (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame) (before : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (owner : Nat) (id : AllocId) (offset : Nat) (len : UInt64)
    (W : UniformWindow before tracker data owner id offset len.toNat .mut) (place : MPlaceTy Provenance) where
  model : DuplicatePrefixCallModel.Model options remaining span before
  state : DuplicatePrefixRuntimeInput.State before tracker
  highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag
  rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout)
  borrowFrame : FrameState
  frameBorrow : root.frame.extra.borrowTracker=some borrowFrame
  binding : CandidateCallBindings.WindowBinding before W.pointer.value id offset len.toNat
  positive : 0<len.toNat
  signedFits : len.toNat<9223372036854775808
  tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615
  sourceShort : W.allocation.extra.nodes.size<65536
  dynamicFuel : Nat
  validationFuel : Nat
  dynamicEq : options.place.dynamicFuel=dynamicFuel+1
  validationEq : options.limits.validation=validationFuel+1
  origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place
  returnOwner : Nat
  V : UniformWindow before tracker data returnOwner physical.id physical.offset.toNat 1 .ret
  returnPointer : physical.pointer=V.pointer.value
  returnBinding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1
  ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1
  boolRoom : V.allocation.extra.nodes.size+2<65536
  sameAllocation : physical.id=id → V.allocation=W.allocation
  sameCompletion : physical.id=id → V.precise.completion=W.precise.completion
  separate : physical.id=id → ∀ byte,Window id offset len.toNat byte → Window physical.id physical.offset.toNat 1 byte → False

private theorem window_runtime {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag) :
    DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global ∧ W.allocation.extra.roots.toList.Nodup := by
  have present := W.present
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨actualId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,equal⟩
  have treeEq : entry.allocation.extra=W.allocation.extra := congrArg Allocation.extra equal
  exact ⟨⟨by simpa only [treeEq] using state.formed (actualId,entry) member,
    by simpa only [treeEq] using state.coherent (actualId,entry) member,
    by simpa only [treeEq] using state.possible (actualId,entry) member,
    by simpa only [treeEq] using highwater (actualId,entry) member⟩,
    by simpa only [treeEq] using state.roots (actualId,entry) member⟩

def action (h : RootCallCore.RootHooks) (value : Immediate Provenance) (count : UInt64) (place : MPlaceTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let _ ← h.withRetagMode () .FnEntry (RootCallCore.argumentBody h ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second count))
  RootEntryTail.tail h place

theorem Conditions.fresh {options remaining span frames root before tracker data owner id offset len W place}
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) :
    tracker.global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  have room := C.tagRoom
  change tracker.global.nextPointerTag.value.toNat<18446744073709551615
  omega

/-- Exact output of the actual argument/Bool/frame-initialization phase. Raw
source and Bool operations remain attached to the same installed machines;
the record is output evidence, not a new caller admission predicate. -/
structure Output {options remaining span frames root before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits)
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place) (count : UInt64) where
  sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  sourceOutput : GeneralBorrowForestFnEntry.Output
  sourceChild : UniIndex
  sourceLive : before.memory.live.find? (fun row=>row.1==id)=some (id,sourceEntry)
  sourceAllocation : sourceEntry.allocation=W.allocation
  sourceActual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global C.borrowFrame id W.pointer.value.provenance (UInt64.ofNat offset) len=.ok sourceOutput
  sourceTag : sourceOutput.tag=tracker.global.nextPointerTag
  sourceGlobal : sourceOutput.global=(registered tracker.global C.borrowFrame id C.fresh).1
  sourceFrame : sourceOutput.frame=(registered tracker.global C.borrowFrame id C.fresh).2
  sourceWitness : CurrentCallResourceFnEntry.BorrowWitness W sourceOutput sourceChild (UInt64.ofNat offset) len
  argsRoot : RootFrame
  argsRootEq : argsRoot=RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root C.borrowFrame W.pointer.value len id tracker.global.nextPointerTag) count
  sourceMachine : Before
  sourceMachineEq : sourceMachine={CurrentCallTypedSourceCopy.validated before tracker C.fresh id sourceEntry sourceOutput.child.tree with borrowTracker:=some ⟨sourceOutput.global,tracker.retagMode⟩}
  arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩ (second count))
    (Storage.withCurrent frames root.frame before)=.ok (2,2) (Storage.withCurrent frames argsRoot.frame sourceMachine)
  R : CurrentCallPostRole.InstalledRole C.V sourceMachine ⟨sourceOutput.global,tracker.retagMode⟩
  sameTree : C.physical.id=id → R.tree=sourceOutput.child.tree ∧ R.completion=S05ConcreteProtectedChildCompletion.extend W.precise.completion sourceChild W.pointer.grant
  otherTree : C.physical.id≠id → R.tree=C.V.allocation.extra ∧ R.completion=C.V.precise.completion
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow sourceMachine place
  physicalPointer : physical.pointer=C.physical.pointer
  physicalId : physical.id=C.physical.id
  physicalOffset : physical.offset=C.physical.offset
  returnRoom : sourceOutput.global.nextPointerTag.value<18446744073709551615
  boolOutput : GeneralBorrowForestFnEntry.Output
  boolChild : UniIndex
  boolActual : CandidateCurrentFnEntryRaw.operation R.tree sourceOutput.global sourceOutput.frame physical.id C.V.pointer.value.provenance physical.offset 1=.ok boolOutput
  boolTag : boolOutput.tag=sourceOutput.global.nextPointerTag
  boolGlobal : boolOutput.global=(registered sourceOutput.global sourceOutput.frame physical.id returnRoom).1
  boolFrame : boolOutput.frame=(registered sourceOutput.global sourceOutput.frame physical.id returnRoom).2
  boolNode : TreeNode
  boolNodeAt : boolOutput.child.tree.nodes.get boolChild=some boolNode
  boolNodeTag : boolNode.tag=boolOutput.tag
  updated : Allocation Provenance BorrowTree
  updatedExtra : updated.extra=(boolOutput.child.tree.performBorrowAccessRange (.concrete sourceOutput.global.nextPointerTag)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write boolOutput.global.protectedTags .VisitChildrenOfAccessed).tree
  updatedSize : updated.byteSize=physical.entry.allocation.byteSize
  updatedLength : updated.len=physical.entry.allocation.len
  updatedMutable : updated.mutability=.Mut
  mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
    ((physical.entry.allocation.setExtra boolOutput.child.tree).setExtra updated.extra)=.ok () updated
  snapshot : AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation
  updatedNodes : updated.extra.nodes=boolOutput.child.tree.nodes
  updatedRoots : updated.extra.roots=boolOutput.child.tree.roots
  updatedTags : updated.extra.tagMapping=boolOutput.child.tree.tagMapping
  updatedCapacity : updated.extra.locations.size=boolOutput.child.tree.locations.size
  afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra boolOutput.global
  afterParents : ParentInterpretation updated.extra (S05ConcreteProtectedChildCompletion.extend R.completion boolChild C.V.pointer.grant)
  afterOwned : GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority updated.extra
    (S05ConcreteProtectedChildCompletion.extend R.completion boolChild C.V.pointer.grant) boolOutput.global.protectedTags boolChild)
    physical.offset (physical.offset+1) updated.extra.locations
  finalMachine : Before
  finalMachineEq : finalMachine=
    let retagged := borrowedState frames (atSpan argsRoot ⟨601⟩).frame sourceOutput.frame sourceMachine
      ⟨sourceOutput.global,tracker.retagMode⟩ returnRoom physical.id physical.entry boolOutput.child.tree
    {retagged.machine with memory:={retagged.machine.memory with live:=
      ((retagged.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
  protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
    (Storage.withCurrent frames (atSpan argsRoot ⟨601⟩).frame sourceMachine)=.ok () (Storage.withCurrent frames
      (registeredFrame (atSpan argsRoot ⟨601⟩).frame sourceOutput.frame physical.id sourceOutput.global.nextPointerTag) finalMachine)
  tail : RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
    (Storage.withCurrent frames argsRoot.frame sourceMachine)=.ok () (Storage.withCurrent frames
      (CallEntryFacts.doneRootFrame {registeredFrame (atSpan argsRoot ⟨601⟩).frame sourceOutput.frame physical.id sourceOutput.global.nextPointerTag with location:=.unwinding ⟨559⟩}) finalMachine)
  actual : action (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
    (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm count place
    (Storage.withCurrent frames root.frame before)=.ok () (Storage.withCurrent frames
      (CallEntryFacts.doneRootFrame {registeredFrame (atSpan argsRoot ⟨601⟩).frame sourceOutput.frame physical.id sourceOutput.global.nextPointerTag with location:=.unwinding ⟨559⟩}) finalMachine)
  finalTracked : finalMachine.borrowTracker=some ⟨boolOutput.global,tracker.retagMode⟩
  finalIds : (finalMachine.memory.live.toList.map Prod.fst).Nodup
  finalRuntime : ∀ row∈finalMachine.memory.live.toList,DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra boolOutput.global
  finalRoots : ∀ row∈finalMachine.memory.live.toList,row.2.allocation.extra.roots.toList.Nodup
  finalHighwater : ∀ row∈finalMachine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra boolOutput.global.protectedTags boolOutput.global.nextPointerTag

private theorem finish_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (sourceId : AllocId) (sourceTag : BorTag)
    (before sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before)=.ok (2,2) (Storage.withCurrent frames
        (RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count).frame sourceMachine))
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    action (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm count place
      (Storage.withCurrent frames root.frame before)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) ∧
    RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
      (Storage.withCurrent frames (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  let argsRoot := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count
  let protectedFrame := registeredFrame (atSpan argsRoot ⟨601⟩).frame sourceFrame boolId boolTag
  have dead : ∀ slot : Fin 25,slot.val≠1 → slot.val≠2 →
      (protectedFrame.locals[slot.val]'(by simpa only [protectedFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,atSpan] using argsRoot.valid slot)).value=.dead := by
    intro slot ne1 ne2
    have found := CurrentCallSourceArguments.result_other_local options remaining span root borrowFrame pointer len count sourceId sourceTag slot.val ne1 ne2
    rw [rawLocals] at found
    have raw : (Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))[slot.val]?=some ⟨.dead,none⟩ := by simp [slot.isLt]
    have cell : argsRoot.frame.locals[slot.val]?=some ⟨.dead,none⟩ := found.trans raw
    have exactCell := Option.some.inj ((Array.getElem?_eq_getElem (argsRoot.valid slot)).symm.trans cell)
    exact congrArg LocalState.value exactCell
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span frames protectedFrame finalMachine
    argsRoot.body argsRoot.size (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide)) argsRoot.noClocks
  have tail := CurrentCallSourceArguments.tail_of_steps options limits (remaining+1) span frames argsRoot sourceMachine place _ _ protection finish
  refine ⟨?_,tail⟩
  unfold action
  simp only [bind,EStateM.bind]
  rw [arguments]
  exact tail

/-- The normalized positive source/return resources drive the real argument
and destination operations on one machine. No caller success certificates or
legacy proposal are consumed. This phase begins at the actual raw root frame. -/
theorem invoke {options remaining span frames root before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits)
    (C : Conditions options remaining span frames root before tracker data owner id offset len W place)
    (count : UInt64) : Nonempty (Output limits C count) := by
  obtain ⟨runtime,distinct⟩ := window_runtime W C.state C.highwater
  obtain ⟨returnRuntime,_⟩ := window_runtime C.V C.state C.highwater
  have contexts := DuplicatePrefixCallModel.contexts options remaining span before C.model
  obtain ⟨ctx⟩ := contexts.1
  obtain ⟨retagCtx⟩ := contexts.2.2.2
  let prepared := firstLive root
  have frameBorrow : prepared.frame.extra.borrowTracker=some C.borrowFrame := C.frameBorrow
  have live1 : (prepared.frame.locals[1]'(prepared.valid i1)).value=.live (.immediate .uninit) := by
    simp only [prepared,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cache1 : (prepared.frame.locals[1]'(prepared.valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [prepared,firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by have h:=C.sourceShort;omega
  obtain ⟨entry,sourceOutput,sourceChild,sourceLive,sourceAllocation,sourceActual,sourceTag,sourceGlobal,sourceFrame,⟨sourceWitness⟩,
    checked,copy,scopedCopy,sourceTracked,sourceInstalled,sourceIssued,frameSource,returnPlace,continuation,varargs,
    body,identity,callee,location,clocks,size,localValue,sourceGhost,postOrigins,types,addresses,threads,dataRace,
    sourceState,sourceHighwater,⟨R,sameTree,otherTree⟩⟩ :=
    CurrentCallResourcePairSource.invoke options limits remaining span ctx before tracker data owner id offset len W runtime C.state C.highwater
      frames prepared.frame C.borrowFrame frameBorrow C.binding C.positive C.signedFits C.fresh distinct C.sourceShort nodeRoom C.model.noDataRace
      C.model.nullComparator C.dynamicFuel C.validationFuel C.dynamicEq C.validationEq C.model.metadata C.origins C.model.debugOff
      C.model.ghostOff C.model.shallow 1 (prepared.valid i1) .uninit live1 cache1 prepared.noClocks
      C.returnOwner C.physical.id C.physical.offset.toNat C.V returnRuntime C.sameAllocation C.sameCompletion C.separate
  let sourceAfter := CurrentCallTypedSourceCopy.validated before tracker C.fresh id entry sourceOutput.child.tree
  let sourceMachine : Before := {sourceAfter with borrowTracker:=some ⟨sourceOutput.global,tracker.retagMode⟩}
  let nextFn : MachineHooks.BorrowState := ⟨sourceOutput.global,.FnEntry⟩
  let argsRoot := RootArgumentsTwo.result
    (CurrentCallSourceArguments.doneRoot options remaining span root C.borrowFrame W.pointer.value len id tracker.global.nextPointerTag) count
  have sourceAfterTracked : sourceAfter.borrowTracker=some nextFn := by
    change sourceAfter.borrowTracker=some ⟨sourceOutput.global,.FnEntry⟩
    rw [sourceGlobal]
    rfl
  have arguments := (CurrentCallSourceArguments.arguments options limits remaining span C.model.debugOff C.validationFuel C.validationEq
    frames root C.rawLocals before sourceAfter tracker nextFn C.state.enabled sourceAfterTracked C.model.ghostOff C.model.shallow
    (by rfl) C.model.shallow C.borrowFrame W.pointer.value len count id tracker.global.nextPointerTag copy).2
  have memory : sourceMachine.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=entry.allocation.setExtra sourceOutput.child.tree}) := rfl
  obtain ⟨physical,physicalPointer,physicalId,physicalOffset,_,binding⟩ := CurrentCallBoolTreeWindow.replace
    C.physical C.returnBinding id entry sourceLive sourceOutput.child.tree addresses memory
  have physicalPresent : Present (ActualWorld sourceMachine) physical.id physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live),rfl⟩
  have rolePresent : Present (ActualWorld sourceMachine) physical.id (C.V.allocation.setExtra R.tree) := by rw [physicalId];exact R.present
  have ids : ((ActualWorld sourceMachine).toList.map Prod.fst).Nodup := by
    simpa [ActualWorld,List.map_map,Function.comp_def] using sourceState.allocationIds
  have allocation := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld sourceMachine).toList ids physical.id
    physical.entry.allocation (C.V.allocation.setExtra R.tree) physicalPresent rolePresent
  obtain ⟨boundEntry,base,boundLive,cached,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := C.binding
  have entryEq : boundEntry=entry := (Prod.mk.inj (Option.some.inj (boundLive.symm.trans sourceLive))).2
  subst boundEntry
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,W.issued.capability.treeExtent,←W.issued.capability.extent,←sourceAllocation]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;have positive:=C.positive;rw [zero] at positive;cases positive
  have growth := CurrentCallResourceBorrowGrowth.operation W runtime C.state C.highwater C.borrowFrame C.fresh (by simp [demandOf])
    distinct C.sourceShort nodeRoom (UInt64.ofNat offset) len startEq rfl nonzero bounds sourceOutput sourceActual
  have boolShort : R.tree.nodes.size+1<65536 := by
    by_cases same : C.physical.id=id
    · rw [(sameTree same).1]
      have alloc := C.sameAllocation same
      rw [←alloc] at growth
      have room := C.boolRoom
      omega
    · rw [(otherTree same).1]
      have room := C.boolRoom
      omega
  have returnRoom : sourceOutput.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
    have room := C.tagRoom
    rw [sourceGlobal]
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh).value.toNat<18446744073709551615
    omega
  have frameSource : (atSpan argsRoot ⟨601⟩).frame.extra.borrowTracker=some sourceOutput.frame := by
    rw [sourceFrame]
    exact CurrentCallSourceArguments.result_borrowFrame options remaining span root C.borrowFrame W.pointer.value len count id tracker.global.nextPointerTag
  have ready : CurrentCallBoolProtection.WindowReady sourceMachine physical.id physical.offset.toNat 1 := by
    rw [physicalId,physicalOffset]
    exact C.ready.transport rfl
  obtain ⟨boolOutput,boolChild,boolActual,boolTag,boolGlobal,boolFrame,rawParents,rawOwned,rawNode,updated,
    protection,extra,bytes,byteLength,mutable,mutation,snapshot,retaggedTracked,frameTracked,destination,
    updatedRuntime,updatedParents,updatedOwned,updatedNodes,updatedRoots,updatedTags,updatedCapacity,
    finalTracked,finalIds,finalTags,finalRuntime,finalRoots,finalHighwater,finalActual⟩ :=
    CurrentCallPostRole.protect_role options limits (remaining+1) span retagCtx sourceMachine ⟨sourceOutput.global,tracker.retagMode⟩
      frames (atSpan argsRoot ⟨601⟩).frame sourceOutput.frame sourceState sourceHighwater frameSource place physical C.V R
      physicalId (congrArg UInt64.toNat physicalOffset) (physicalPointer.trans C.returnPointer) allocation binding returnRoom boolShort
      sourceGhost (dataRace.trans C.model.noDataRace) C.model.noBackend ready
  let retagged := borrowedState frames (atSpan argsRoot ⟨601⟩).frame sourceOutput.frame sourceMachine
    ⟨sourceOutput.global,tracker.retagMode⟩ returnRoom physical.id physical.entry boolOutput.child.tree
  let finalMachine : Before := {retagged.machine with memory:={retagged.machine.memory with live:=
    ((retagged.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
  obtain ⟨boolNode,boolNodeAt,boolNodeTag⟩ := rawNode
  have allocationMutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      ((physical.entry.allocation.setExtra boolOutput.child.tree).setExtra updated.extra)=.ok () updated := by
    rw [extra]
    exact mutation
  have actualExtra : updated.extra=(boolOutput.child.tree.performBorrowAccessRange (.concrete sourceOutput.global.nextPointerTag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write boolOutput.global.protectedTags .VisitChildrenOfAccessed).tree := by
    rw [boolGlobal]
    exact extra
  have completed := finish_of_arguments options limits remaining span frames root C.rawLocals C.borrowFrame W.pointer.value len count id tracker.global.nextPointerTag
    before sourceMachine finalMachine sourceOutput.frame physical.id sourceOutput.global.nextPointerTag place arguments protection
  exact ⟨⟨entry,sourceOutput,sourceChild,sourceLive,sourceAllocation,sourceActual,sourceTag,sourceGlobal,sourceFrame,sourceWitness,
    argsRoot,rfl,sourceMachine,rfl,arguments,R,sameTree,otherTree,physical,physicalPointer,physicalId,physicalOffset,returnRoom,boolOutput,boolChild,
    boolActual,boolTag,boolGlobal,boolFrame,boolNode,boolNodeAt,boolNodeTag,updated,actualExtra,bytes,byteLength,mutable,allocationMutation,snapshot,
    updatedNodes,updatedRoots,updatedTags,updatedCapacity,updatedRuntime,updatedParents,updatedOwned,finalMachine,rfl,protection,completed.2,completed.1,
    finalTracked,finalIds,finalRuntime,finalRoots,finalHighwater⟩⟩

end
end DuplicatePrefix.CurrentCallResourceEntryBody
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceEntryBody" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource entry-body dependency {dependency}"
