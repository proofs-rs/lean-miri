import duplicate_prefix.CurrentCallCheckpointSharedFacts
import duplicate_prefix.CurrentCallCheckpointLen
import duplicate_prefix.CurrentCallLenArgumentCopy
import duplicate_prefix.RelevanceCurrent

namespace DuplicatePrefix.CurrentCallCheckpointLenControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateCurrentJointCall CurrentCallPostEntryCheckpoint
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend GeneralBorrowForestMixedLenBeforeReturn
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

variable {options remaining span len count place} (checkpoint : Checkpoint options remaining span len count place)

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
  {checkpoint.sourceEntry with allocation:=checkpoint.sourceEntry.allocation.setExtra (CurrentCallCheckpointShared.tree checkpoint)}

def borrowedTree : BorrowTree:=CurrentCallLenArgumentCopy.finalTree (entry checkpoint).allocation.extra
  (CurrentCallCheckpointShared.tracker checkpoint) checkpoint.tracker.global.nextPointerTag (UInt64.ofNat checkpoint.offset) len

theorem room : (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag.value<18446744073709551615:=by
  have successor:=GenericFunctionEntryNumerics.successor_value checkpoint.tracker.global.nextPointerTag (CurrentCallCheckpointShared.room checkpoint)
  apply UInt64.lt_iff_toNat_lt.mpr
  change (TypedRetagEmpty.successorTag checkpoint.tracker.global.nextPointerTag (CurrentCallCheckpointShared.room checkpoint)).value.toNat<18446744073709551615
  rw [successor]
  have budget:=checkpoint.tags
  omega

def helperFrame : FrameState:=({} : FrameState).addProtector checkpoint.source.role.backing.id
  (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag

def held : MachineHooks.BorrowState:=TypedBorrowSteps.registeredTracker
  (ReferenceBorrowDriver.allocatedTracker (CurrentCallCheckpointShared.tracker checkpoint) (room checkpoint))
  (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag

def releasedTree : BorrowTree:=((borrowedTree checkpoint).releaseProtector
  (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag (held checkpoint).global.protectedTags).tree

def postTracker : MachineHooks.BorrowState:={held checkpoint with global:=(held checkpoint).global.endCall (helperFrame checkpoint)}

def helperIndex : UniIndex:=((borrowedTree checkpoint).indexOfTag (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag).getD ⟨0⟩

private theorem model_transport {options remaining span} (before after : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (user : after.user=before.user) (threads : after.threads=before.threads) (race : after.dataRace=before.dataRace)
    (defaultTracker : ∃tracker,after.borrowTracker=some tracker ∧tracker.retagMode=.Default) :
    DuplicatePrefixCallModel.Model options remaining span after:=by
  exact {model with
    ghostOff:=by rw [user];exact model.ghostOff
    shallow:=by rw [user];exact model.shallow
    defaultTracker:=defaultTracker
    noDataRace:=race.trans model.noDataRace
    noBackend:=by rw [user];exact model.noBackend
    metadata:=by rw [user];exact model.metadata
    fixedScheduler:=by rw [threads];exact model.fixedScheduler
    unchecked:=by rw [user];exact model.unchecked
    noGc:=by rw [user];exact model.noGc}

theorem model : DuplicatePrefixCallModel.Model options remaining span (CurrentCallCheckpointShared.machine checkpoint):=by
  have original:=checkpoint.model
  have flags:=RootZeroCompleteState.tick_flags options remaining span checkpoint.machine
  have unchecked:=original.unchecked
  have noGc:=original.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  have tickModel : DuplicatePrefixCallModel.Model options remaining span (CurrentCallCheckpointShared.before checkpoint):=by
    unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
    rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
    exact {original with
      unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
      noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}
  exact model_transport _ _ tickModel rfl rfl rfl ⟨CurrentCallCheckpointShared.tracker checkpoint,rfl,checkpoint.mode⟩

private theorem local_cell (locals : Array (LocalState Provenance LocalLayout)) (id : Nat)
    (valid : id<locals.size) (value : Immediate Provenance) (layout : LocalLayout)
    (stored : locals[id]?=some ⟨.live (.immediate value),some layout⟩) :
    locals[id].value=.live (.immediate value) ∧locals[id].layout=some layout := by
  have equal:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans stored)
  rw [equal]
  exact ⟨rfl,rfl⟩

private theorem afterPush_types (machine : Before) (size : Nat) (newRank oldRank : UInt8) :
    (GenericPushRelevance.afterPush machine size newRank oldRank).user.payload.payload.user.types=machine.user.payload.payload.user.types:=by
  unfold GenericPushRelevance.afterPush
  split <;>rfl

structure Returned (limits : ExecutionMachine.Limits) (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count) (base : UInt64) where
  helper : CompilerFrameContext.ActualFrame
  machine : Before
  trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] (CurrentCallCheckpointSharedFacts.caller checkpoint frame shape base) (CurrentCallCheckpointShared.machine checkpoint))
    (Storage.withCurrent #[(cachedCaller (CurrentCallCheckpointSharedFacts.caller checkpoint frame shape base)
      (by rw [CurrentCallCheckpointSharedFacts.size];decide))] helper machine)
  location : helper.location=.mir ⟨1,1⟩
  returned : helper.locals[0]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩
  protector : helper.extra.borrowTracker=some (({} : FrameState).addProtector checkpoint.source.role.backing.id
    (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag)
  clocks : helper.extra.dataRace=none
  destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace 0
    (cachedCaller (CurrentCallCheckpointSharedFacts.caller checkpoint frame shape base)
      (by rw [CurrentCallCheckpointSharedFacts.size];decide)) 11 RootCompilerFacts.usizeLayout
  continuation : helper.returnContinuation=.goto (some 3) .Continue
  varargs : helper.vaList=#[]
  memory : machine.memory=RetagEntry.updatedMemory (CurrentCallCheckpointShared.machine checkpoint).memory
    checkpoint.source.role.backing.id (entry checkpoint) (borrowedTree checkpoint)
  tracked : machine.borrowTracker=some (TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker (CurrentCallCheckpointShared.tracker checkpoint) (room checkpoint))
    (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag)
  ghost : machine.user.payload.ghost=false
  shallow : machine.user.payload.validation=.Shallow
  race : machine.dataRace=none
  addresses : machine.user.addresses=(CurrentCallCheckpointShared.machine checkpoint).user.addresses
  types : machine.user.payload.payload.user.types=(CurrentCallCheckpointShared.machine checkpoint).user.payload.payload.user.types
  extras : machine.user.payload.payload.user.runtime.extras=(CurrentCallCheckpointShared.machine checkpoint).user.payload.payload.user.runtime.extras
  facts : ReturnFacts options remaining span helper machine len
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete checkpoint.source.role.backing.id (CurrentCallCheckpointShared.tracker checkpoint).global.nextPointerTag)
        (Size.ofBytes (base+UInt64.ofNat checkpoint.offset))) len SharedReferenceMetadata.sharedLayout).imm
  cache : RootCache #[] machine

theorem source_live {limits frame shape base} (returned : Returned checkpoint limits frame shape base) :
    returned.machine.memory.live.find? (fun row=>row.1==checkpoint.source.role.backing.id)=
      some (checkpoint.source.role.backing.id,{entry checkpoint with allocation:=(entry checkpoint).allocation.setExtra (borrowedTree checkpoint)}):=by
  rw [returned.memory]
  exact StackPopRelease.lookup_commit_same _ _ _ _

theorem source_present {limits frame shape base} (returned : Returned checkpoint limits frame shape base) :
    CandidateStableCallOwnership.Present (CandidateCurrentJointCall.ActualWorld returned.machine)
      checkpoint.source.role.backing.id ((entry checkpoint).allocation.setExtra (borrowedTree checkpoint)):=by
  simp only [CandidateStableCallOwnership.Present,CandidateCurrentJointCall.ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (source_live checkpoint returned)),rfl⟩

/-- Only the common typed Len execution leaf is used. The two certificates
are internal outputs of the spatial logical producer at the public join. -/
private theorem before_return (limits : ExecutionMachine.Limits) (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (frame : CompilerFrameContext.ActualFrame) (shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count)
    (base : UInt64)
    (cached : (CurrentCallCheckpointShared.before checkpoint).user.addresses.baseAddr.find? (fun row=>row.allocId==checkpoint.source.role.backing.id)=
      some ⟨checkpoint.source.role.backing.id,base⟩)
    (nonnull : base+UInt64.ofNat checkpoint.offset≠0)
    (readDone : (CurrentCallLenArgumentCopy.readOperation (entry checkpoint).allocation.extra
      (CurrentCallCheckpointShared.tracker checkpoint) checkpoint.tracker.global.nextPointerTag (UInt64.ofNat checkpoint.offset) len).status=.Completed)
    (childDone : (CurrentCallLenArgumentCopy.childOperation (entry checkpoint).allocation.extra
      (CurrentCallCheckpointShared.tracker checkpoint) checkpoint.tracker.global.nextPointerTag (UInt64.ofNat checkpoint.offset) len).outcome=.ok ()) :
    Nonempty (Returned checkpoint limits frame shape base):=by
  let beforeMachine:=CurrentCallCheckpointShared.machine checkpoint
  let machine:=PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  let current:=CurrentCallCheckpointShared.tracker checkpoint
  let rValue:=CurrentCallCheckpointSharedFacts.readerValue checkpoint base
  have callerSize:=CurrentCallCheckpointSharedFacts.size checkpoint frame shape base
  have sourceSlot:=CurrentCallCheckpointSharedFacts.slot12 checkpoint frame shape base
  have slot11:=CurrentCallCheckpointSharedFacts.slot11 checkpoint frame shape base
  have body:=CurrentCallCheckpointSharedFacts.body checkpoint frame shape base
  have identity:=CurrentCallCheckpointSharedFacts.identity checkpoint frame shape base
  have callee:=CurrentCallCheckpointSharedFacts.callee checkpoint frame shape base
  have noClocks:=CurrentCallCheckpointSharedFacts.noClocks checkpoint frame shape base
  have located:=CurrentCallCheckpointSharedFacts.location checkpoint frame shape base
  generalize callerEq : CurrentCallCheckpointSharedFacts.caller checkpoint frame shape base=caller at callerSize sourceSlot slot11 body identity callee noClocks located
  have v11 : 11<caller.locals.size:=by rw [callerSize];decide
  have v12 : 12<caller.locals.size:=by rw [callerSize];decide
  have capacity : (entry checkpoint).allocation.extra.locations.size=(entry checkpoint).allocation.byteSize:=by
    have shared:=(CurrentCallCheckpointShared.operation checkpoint).2.2.2.1
    change (CurrentCallCheckpointShared.tree checkpoint).locations.size=checkpoint.sourceEntry.allocation.byteSize
    rw [checkpoint.sourceAllocation]
    refine shared.trans ?_
    let byte:=(checkpoint.source.role.backing.id,checkpoint.offset)
    have hit : CandidateStableCallOwnership.Window checkpoint.source.role.backing.id checkpoint.offset len.toNat byte:=
      ⟨rfl,Nat.le_refl _,by have p:=checkpoint.source.positive;dsimp only [byte];omega⟩
    obtain ⟨i,inside⟩:=checkpoint.source.role.covered byte hit
    exact (checkpoint.source.role.roles i ⟨byte,hit,inside⟩).issued.capability.treeExtent
  have bounds : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤(entry checkpoint).allocation.byteSize.bytes.toNat:=by
    have known:=CurrentCallCheckpointShared.bounds checkpoint
    have shared:=(CurrentCallCheckpointShared.operation checkpoint).2.2.2.1
    rw [←shared] at known
    rw [←capacity]
    exact known
  have sourceModel:=model checkpoint
  obtain ⟨ctx⟩:=ActualReferenceContext.exists_context options remaining span sourceModel.preciseOff sourceModel.implicitOff
  have enabled : machine.borrowTracker=some current:=rfl
  have machineData : machine.user.addresses=(CurrentCallCheckpointShared.before checkpoint).user.addresses ∧
      machine.user.payload.payload.user.types=(CurrentCallCheckpointShared.before checkpoint).user.payload.payload.user.types ∧
      machine.user.payload.payload.user.backend=(CurrentCallCheckpointShared.before checkpoint).user.payload.payload.user.backend:=by
    dsimp only [machine,beforeMachine,CurrentCallCheckpointShared.machine,CurrentCallSpatialSharedInstall.machine,
      ReferenceBorrowDriver.allocatedMachine,PtrMetadataReturn.accountedMachine,SourceControl.accounted]
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl⟩
  have currentCached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==checkpoint.source.role.backing.id)=
      some ⟨checkpoint.source.role.backing.id,base⟩:=by rw [machineData.1];exact cached
  have currentLive : machine.memory.live.find? (fun row=>row.1==checkpoint.source.role.backing.id)=
      some (checkpoint.source.role.backing.id,entry checkpoint):=StackPopRelease.lookup_commit_same _ _ _ _
  have currentGhost : machine.user.payload.ghost=false:=by rw [PtrMetadataReturn.accounted_ghost];exact sourceModel.ghostOff
  have currentShallow : machine.user.payload.validation=.Shallow:=by rw [PtrMetadataReturn.accounted_validation];exact sourceModel.shallow
  have cell11 : caller.locals[11]=⟨.live (.immediate .uninit),none⟩:=Option.some.inj ((Array.getElem?_eq_getElem v11).symm.trans slot11)
  have sourceData:=local_cell caller.locals 12 v12 rValue SharedReferenceMetadata.sharedLayout sourceSlot
  have currentActive : machine.threads.activeThread?=some checkpoint.thread:=by
    change checkpoint.machine.threads.activeThread?=some checkpoint.thread
    exact checkpoint.active
  let rootCaller:=cachedCaller caller v11
  let destination:=(LocalPlaces.localRuntimePlace 0 rootCaller 11 RootCompilerFacts.usizeLayout).stackView
  let pushed:=LenPush.pushed options.userRelevantCrates (Storage.withCurrent #[] rootCaller machine) destination
  have pushedSize : pushed.stack.frames.size=2:=rfl
  obtain ⟨index,currentFrame,top,presentFrame⟩:=RelevanceCurrent.exists_current pushed.stack.frames checkpoint.thread
    (by rw [pushedSize];decide) (by intro index found;rw [checkpoint.top] at found;have zero:=Option.some.inj found;subst index;rw [pushedSize];decide)
  have pushedTypes : EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootCaller machine) destination currentFrame)=machine.user.payload.payload.user.types:=by
    let supply:=LenPush.fresh machine
    let helperFrame:=LenFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2
    change (GenericPushRelevance.afterPush supply.1 1 helperFrame.extra.userRelevance currentFrame.extra.userRelevance).user.payload.payload.user.types=_
    rw [afterPush_types]
    rfl
  have metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootCaller machine) destination currentFrame)).metadata=PreparedReflection.actual.runtime:=by
    rw [pushedTypes,machineData.2.1]
    exact sourceModel.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootCaller machine) destination currentFrame)):=by
    rw [pushedTypes,machineData.2.1]
    unfold CurrentCallCheckpointShared.before RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact checkpoint.origins
  obtain ⟨helper,post,⟨trace,location,returned,frameTracked,clocks,dest,cont,va,memory,tracked,ghost,shallow,race,addresses,types,extras⟩,facts,cache⟩:=
    CurrentCallLenArgumentCopy.before_return options limits remaining budget dispatch span ctx sourceModel.debugOff sourceModel.nullComparator
      checkpoint.dynamicFuel checkpoint.validationFuel checkpoint.dynamicEq checkpoint.validationEq checkpoint.source.role.backing.id (entry checkpoint)
      base (UInt64.ofNat checkpoint.offset) len checkpoint.tracker.global.nextPointerTag
      (UInt64.lt_iff_toNat_lt.mpr checkpoint.source.positive) nonnull checkpoint.source.signedFits #[] caller machine current enabled checkpoint.mode
      (room checkpoint) readDone childDone bounds capacity v11 (by rw [cell11]) (by rw [cell11]) noClocks currentGhost currentShallow currentCached currentLive
      sourceModel.noDataRace checkpoint.thread index currentFrame currentActive top presentFrame metadata origins body identity callee located
      (DuplicatePrefixCallModel.sourceComparator options remaining span _ sourceModel) v12 sourceData.1 sourceData.2 (machineData.2.2.trans sourceModel.noBackend)
      beforeMachine rfl sourceModel.unchecked sourceModel.noGc sourceModel.fixedScheduler
  refine ⟨⟨helper,post,?_,location,returned,frameTracked,clocks,?_,cont,va,memory,tracked,ghost,shallow,race,addresses,types,extras,facts,cache⟩⟩
  · simpa only [callerEq,beforeMachine,ActualReferenceContext.config,Array.push_empty] using trace
  · simpa only [callerEq,Array.size_empty] using dest

/-- The single common nonzero continuation derives the logical helper
operations internally and runs the existing typed call/body to its Return. -/
theorem invoke (limits : ExecutionMachine.Limits) (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (nonzero : count≠0) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      ∃ shape : GenericFunctionEntryPrefix.Shape checkpoint.frame frame count,
        ∃ base : UInt64,∃ returned : Returned checkpoint limits frame shape base,
          SuccessfulTrace.Trace (config options (remaining+1) span) limits
            (Storage.withCurrent #[] checkpoint.frame checkpoint.machine)
            (Storage.withCurrent #[(cachedCaller (CurrentCallCheckpointSharedFacts.caller checkpoint frame shape base)
              (by rw [CurrentCallCheckpointSharedFacts.size];decide))] returned.helper returned.machine):=by
  obtain ⟨frame,shape,base,cached,pointer,nonnull,sharedTrace⟩:=CurrentCallCheckpointSharedControl.invoke checkpoint limits nonzero
  let prepared:=CurrentCallCheckpointLen.prepared checkpoint
  have readDone:=(CurrentCallCheckpointLen.operations checkpoint).1
  have childDone:=(CurrentCallCheckpointLen.operations checkpoint).2.1
  change (CurrentCallLenArgumentCopy.readOperation prepared.source.backing.allocation.extra
    (CurrentCallCheckpointShared.tracker checkpoint) prepared.readerNode.tag (UInt64.ofNat checkpoint.offset) len).status=.Completed at readDone
  change (CurrentCallLenArgumentCopy.childOperation prepared.source.backing.allocation.extra
    (CurrentCallCheckpointShared.tracker checkpoint) prepared.readerNode.tag (UInt64.ofNat checkpoint.offset) len).outcome=.ok () at childDone
  rw [prepared.tree,prepared.readerTag] at readDone childDone
  obtain ⟨returned⟩:=before_return checkpoint limits budget dispatch frame shape base cached nonnull readDone childDone
  exact ⟨frame,shape,base,returned,SuccessfulTrace.append sharedTrace returned.trace⟩

end
end DuplicatePrefix.CurrentCallCheckpointLenControl

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common Len control dependency {dependency}"
