import duplicate_prefix.CurrentCallEmptyEntryControl
import duplicate_prefix.CurrentCallEmptyUnlocatedCopy
import duplicate_prefix.CurrentCallSelectedBoolProtection
import duplicate_prefix.CurrentCallResourcePreparedEntry

/-! Actual integer-encoded empty source entry. The source creates no family,
node or protector. Both actual argument copies and typed Bool protection are
derived internally from initial physical/runtime data and current Bool ownership. -/
namespace DuplicatePrefix.CurrentCallEmptyIntegerEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem firstFresh (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615) :
    tracker.global.nextPointerTag.value<18446744073709551615 :=
  UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)

def argsRoot (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace=none) (address count : UInt64) : RootFrame :=
  let root := CurrentCallSpatialEntryControl.root before frames place race
  let effect : Effect options (CurrentCallPush.preparedMachine before frames) tracker (.integer address) := .integer address
  RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}) count

def sourceFnMachine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace=none) (address : UInt64)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) : Before :=
  let root := CurrentCallSpatialEntryControl.root before frames place race
  let effect : Effect options (CurrentCallPush.preparedMachine before frames) tracker (.integer address) := .integer address
  (TypedRetagEmpty.afterTag (Storage.withCurrent frames
    (CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}).frame
    (ScopedFrame.entered (CurrentCallPush.preparedMachine before frames) tracker .FnEntry))
    {tracker with retagMode:=.FnEntry} fresh).machine

def sourceMachine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace=none) (address : UInt64)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) : Before :=
  {sourceFnMachine options remaining span before tracker frames place race address fresh with
    borrowTracker:=some {tracker with global:=GeneralBorrowFnEntryRegistration.advanced tracker.global fresh}}

/-- No source allocation/family appears in this actual entry producer. All
operation equations and post-copy facts are conclusions from initial data. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness before frames)
    (address count : UInt64) (nonzero : address≠0)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types) :
    let fresh := firstFresh tracker tagRoom
    let source := sourceMachine options remaining span before tracker frames place model.noDataRace address fresh
    let next := {tracker with global:=GeneralBorrowFnEntryRegistration.advanced tracker.global fresh}
    let args := argsRoot options remaining span before tracker frames place model.noDataRace address count
    ∃ Q : UniformWindow source next data owner physical.id physical.offset.toNat 1 .ret,
    ∃ (boolOutput : GeneralBorrowForestFnEntry.Output) (boolChild : UniIndex),
      Q.pointer=B.pointer ∧ Q.allocation=B.allocation ∧ Q.precise=B.precise ∧
      CandidateCurrentFnEntryRaw.operation Q.allocation.extra next.global {} physical.id Q.pointer.value.provenance physical.offset 1=.ok boolOutput ∧
      boolOutput.tag=next.global.nextPointerTag ∧
      boolOutput.global.rootTag? physical.id=tracker.global.rootTag? physical.id ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness Q boolOutput boolChild physical.offset 1) ∧
    ∃ (updated : Allocation Provenance BorrowTree) (finalMachine : Before),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.integer address) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
          {registeredFrame (atSpan args ⟨601⟩).frame {} physical.id next.global.nextPointerTag with location:=.unwinding ⟨559⟩}) finalMachine) ∧
      finalMachine.memory.live=
        ((((source.memory.live.filter (fun row=>row.1!=physical.id)).push
          (physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra boolOutput.child.tree})).filter
          (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated})) ∧
      finalMachine.borrowTracker=some ⟨boolOutput.global,tracker.retagMode⟩ ∧
      finalMachine.user=source.user ∧ finalMachine.threads=source.threads ∧ finalMachine.dataRace=source.dataRace ∧
      finalMachine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{physical.entry with allocation:=updated}) ∧
      updated.extra=(boolOutput.child.tree.performBorrowAccessRange (.concrete next.global.nextPointerTag)
        (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write boolOutput.global.protectedTags .VisitChildrenOfAccessed).tree ∧
      updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      (registeredFrame (atSpan args ⟨601⟩).frame {} physical.id next.global.nextPointerTag).extra.borrowTracker=
        some (({} : FrameState).addProtector physical.id next.global.nextPointerTag) ∧
      (registeredFrame (atSpan args ⟨601⟩).frame {} physical.id next.global.nextPointerTag).returnPlace=args.frame.returnPlace ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len=updated.byteSize ∧
      updated.mutability=.Mut ∧
      Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra boolOutput.child.tree).setExtra updated.extra)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation := by
  dsimp only
  let fresh := firstFresh tracker tagRoom
  let prepared := CurrentCallPush.preparedMachine before frames
  let root := CurrentCallSpatialEntryControl.root before frames place model.noDataRace
  let effect : Effect options prepared tracker (.integer address) := .integer address
  let d1 := CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}
  let fnMachine := sourceFnMachine options remaining span before tracker frames place model.noDataRace address fresh
  let source := sourceMachine options remaining span before tracker frames place model.noDataRace address fresh
  let next := {tracker with global:=GeneralBorrowFnEntryRegistration.advanced tracker.global fresh}
  let fnTracker := {tracker with global:=GeneralBorrowFnEntryRegistration.advanced tracker.global fresh,retagMode:=.FnEntry}
  let args := argsRoot options remaining span before tracker frames place model.noDataRace address count
  have preparedModel := CurrentCallResourcePreparedEntry.model model frames
  have rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  have frameBorrow : (firstLive root).frame.extra.borrowTracker=some {} :=
    RootEntryFrame.raw_borrow prepared (.memory place) (CallEntryFacts.freshRoot before).2 tracker enabled
  have live1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  have copy := ReferenceArgumentCopy.copy_empty_argument options limits remaining span model.nullComparator model.preciseOff model.implicitOff model.debugOff
    dynamicFuel validationFuel dynamicEq validationEq frames (firstLive root).frame
    (ScopedFrame.entered prepared tracker .FnEntry) 1 .uninit ((firstLive root).valid i1) live1 cached1 (firstLive root).noClocks
    model.ghostOff model.shallow address nonzero {tracker with retagMode:=.FnEntry} rfl rfl fresh model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView rfl
  have copyStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.integer address) 0)
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered prepared tracker .FnEntry))=
      .ok () (Storage.withCurrent frames d1.frame fnMachine) := copy
  obtain ⟨Q,pointerQ,allocationQ,preciseQ,runtimeQ⟩ := CurrentCallEmptyUnlocatedCopy.advance B runtime fresh source rfl
  let P : CandidateCurrentBoolUninitWrite.PhysicalWindow source place := {physical with}
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value]
    exact tagRoom
  have protectedFrameBorrow : (atSpan args ⟨601⟩).frame.extra.borrowTracker=some {} := frameBorrow
  obtain ⟨ctx⟩ := (DuplicatePrefixCallModel.contexts options remaining span before model).2.2.2
  obtain ⟨boolOutput,boolChild,actual,tag,global,frameEq,⟨witness⟩,updated,protection,extra,bytes,length,mutable,write,snapshot,tracked,registeredBorrow,returnPlace⟩ :=
    CurrentCallSelectedBoolProtection.protect options limits (remaining+1) span ctx source next data owner frames
      (atSpan args ⟨601⟩).frame {} rfl protectedFrameBorrow place P Q (pointer.trans (congrArg PointerInstance.value pointerQ).symm)
      (allocation.trans allocationQ.symm) runtimeQ binding (by rw [allocationQ];exact distinct) freshAfter
      (by rw [allocationQ];exact nodeRoom) model.ghostOff model.noDataRace model.noBackend ready
  let retagged := borrowedState frames (atSpan args ⟨601⟩).frame {} source next freshAfter physical.id physical.entry boolOutput.child.tree
  let finalMachine : Before := {retagged.machine with memory:={retagged.machine.memory with live:=
    ((retagged.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
  have protectedStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan args ⟨601⟩).frame source)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan args ⟨601⟩).frame {} physical.id next.global.nextPointerTag) finalMachine) := protection
  have entered := CurrentCallEmptyEntryControl.init_of_copy_protect options limits remaining span frames root rawLocals
    prepared tracker (.integer address) effect {} count source finalMachine {} physical.id next.global.nextPointerTag place
    fnTracker fnMachine enabled rfl model.ghostOff model.shallow model.ghostOff model.shallow validationFuel validationEq rfl copyStep
    before model.noDataRace model.debugOff stackReady rfl rfl protectedStep
  have rootTag : boolOutput.global.rootTag? physical.id=tracker.global.rootTag? physical.id := by rw [global];rfl
  have finalTracked : finalMachine.borrowTracker=some ⟨boolOutput.global,tracker.retagMode⟩ := by rw [global];rfl
  have mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra updated.extra)=.ok () updated := by
    rw [extra]
    simpa only [Allocation.setExtra,Allocation.mapExtra] using write
  obtain ⟨_,_,_,_,maskWF,maskLen,_⟩ := CurrentCallBoolWindow.mutation_metadata physical updated.extra updated mutation
  refine ⟨Q,boolOutput,boolChild,pointerQ,allocationQ,preciseQ,actual,tag,rootTag,⟨witness⟩,updated,finalMachine,
    entered,rfl,finalTracked,rfl,rfl,rfl,?_,?_,bytes,length,registeredBorrow,returnPlace,maskWF,maskLen,mutable,?_,snapshot⟩
  · exact MemoryCopyBridge.live_lookup_replaced retagged.machine.memory physical.id _
  · rw [global]
    exact extra
  · rw [extra]
    exact write

end
end DuplicatePrefix.CurrentCallEmptyIntegerEntry
