import duplicate_prefix.CurrentCallEmptyEntryControl
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow
import duplicate_prefix.CurrentCallSelectedBoolProtection
import duplicate_prefix.CurrentCallSelectedBoolWindow
import duplicate_prefix.CurrentCallEmptyConcreteCopy
import duplicate_prefix.CurrentCallEmptyWildcardCopy
import duplicate_prefix.CurrentCallSelectedBoolQuietSource
import duplicate_prefix.CurrentCallEmptyOtherBool

/-! The immediate actual-copy consumer for live empty sources. Source copying
keeps its real zero-byte constructor and frame protector. Only the current
one-byte Bool reservation supplies content authority. -/
namespace DuplicatePrefix.CurrentCallEmptyLiveEntryCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Consume the same real source copy once, execute typed Bool protection, and
install its current child in the exact full call-initialization output. This
lower composition is shared by the concrete and wildcard live producers. -/
theorem init_current_of_copy (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (place : MPlaceTy Provenance)
    (race : initial.dataRace=none) (stackReady : CurrentCallPush.StackReadiness initial frames)
    (debug : options.place.debugAssertions=false)
    (argument : DuplicatePrefixSliceArgument.Argument)
    (effect : Effect options (CurrentCallPush.preparedMachine initial frames) tracker argument)
    (borrowFrame : FrameState) (count : UInt64)
    (sourceFn source : Before) (next : MachineHooks.BorrowState) (sourceFrame : FrameState)
    (enabled : (CurrentCallPush.preparedMachine initial frames).borrowTracker=some tracker)
    (sourceTracked : sourceFn.borrowTracker=some next)
    (sourceEq : source={sourceFn with borrowTracker:=some {next with retagMode:=tracker.retagMode}})
    (ghost : initial.user.payload.ghost=false) (shallow : initial.user.payload.validation=.Shallow)
    (sourceGhost : sourceFn.user.payload.ghost=false) (sourceShallow : sourceFn.user.payload.validation=.Shallow)
    (sourceRace : source.dataRace=none) (backend : source.user.payload.payload.user.backend=.none)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallEmptyEntryControl.value options remaining span argument).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive (CurrentCallSpatialEntryControl.root initial frames place race)).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive (CurrentCallSpatialEntryControl.root initial frames place race)).frame
        (ScopedFrame.entered (CurrentCallPush.preparedMachine initial frames) tracker .FnEntry))=
      .ok () (Storage.withCurrent frames (CurrentCallEmptySourceArguments.doneRoot effect remaining span
        (CurrentCallSpatialEntryControl.root initial frames place race) borrowFrame).frame sourceFn))
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow source place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow source {next with retagMode:=tracker.retagMode} data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra next.global)
    (binding : CandidateCallBindings.WindowBinding source physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (fresh : next.global.nextPointerTag.value<18446744073709551615)
    (room : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady source physical.id physical.offset.toNat 1)
    (sourceBorrow : (atSpan (RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span
      (CurrentCallSpatialEntryControl.root initial frames place race) borrowFrame) count) ⟨601⟩).frame.extra.borrowTracker=some sourceFrame) :
    let root:=CurrentCallSpatialEntryControl.root initial frames place race
    let args:=RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (machine : Before),
    ∃ nextData nextOwner,∃ Q : UniformWindow machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat 1 .ret,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=
        .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
          {registeredFrame (atSpan args ⟨601⟩).frame sourceFrame physical.id output.tag with location:=.unwinding ⟨559⟩}) machine) ∧
      machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      Q.pointer=CurrentCallResourceFnEntry.child_pointer B output.tag child ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra output.global ∧
      Q.allocation.extra.roots.toList.Nodup ∧Q.allocation.extra.nodes.size<65536 ∧
      ∃ node,Q.allocation.extra.nodes.get child=some node ∧node.tag=output.tag ∧node.children=#[] ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra child .Write physical.offset (physical.offset+1) ∧
      SpatialDelegation machine ⟨output.global,tracker.retagMode⟩ physical.id Q.allocation Q.precise.completion B.pointer.grant ∧
      PointerBinds Q.allocation B.pointer ∧
      (registeredFrame (atSpan args ⟨601⟩).frame sourceFrame physical.id output.tag).returnPlace=args.frame.returnPlace ∧
      Q.precise.completion.parents[child.toNat]?=some (some B.pointer.grant) ∧
      CandidateCurrentFnEntryRaw.operation B.allocation.extra next.global sourceFrame physical.id B.pointer.value.provenance physical.offset 1=.ok output ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness B output child physical.offset 1) ∧
      output.tag=next.global.nextPointerTag ∧
      ∃constructor : Before,Present (ActualWorld constructor) physical.id (B.allocation.setExtra output.child.tree) ∧
      output.global.rootTag? physical.id=next.global.rootTag? physical.id ∧
      Q.allocation.extra=(output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed).tree ∧
      machine.memory.live=(source.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=Q.allocation}) ∧
      ∃ window : CurrentCallBoolScalarWrite.Window machine place,
        window.pointer=physical.pointer ∧window.id=physical.id ∧window.offset=physical.offset ∧window.entry.allocation=Q.allocation ∧
        CandidateCallBindings.WindowBinding machine window.pointer window.id window.offset.toNat 1 ∧
        CurrentCallBoolProtection.WindowReady machine window.id window.offset.toNat 1 ∧
        machine.user=source.user ∧machine.threads=source.threads ∧machine.dataRace=source.dataRace := by
  dsimp only
  let root:=CurrentCallSpatialEntryControl.root initial frames place race
  let args:=RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count
  let current:MachineHooks.BorrowState:={next with retagMode:=tracker.retagMode}
  have tracked : source.borrowTracker=some current := by rw [sourceEq]
  have sourceGhost' : source.user.payload.ghost=false := by simpa only [sourceEq] using sourceGhost
  obtain ⟨output,child,actual,tag,global,frameEq,⟨witness⟩,updated,protection,extra,bytes,length,mutable,mutation,snapshot,_,_,returnPlace⟩ :=
    CurrentCallSelectedBoolProtection.protect options limits (remaining+1) span ctx source current data owner frames
      (atSpan args ⟨601⟩).frame sourceFrame tracked sourceBorrow place physical B pointer allocation runtime binding distinct fresh room
      sourceGhost' sourceRace backend ready
  let constructor:=borrowedState frames (atSpan args ⟨601⟩).frame sourceFrame source current fresh physical.id physical.entry output.child.tree
  let machine:Before:={constructor.machine with memory:={constructor.machine.memory with live:=
    ((constructor.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
  have protectedStep : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan args ⟨601⟩).frame source)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan args ⟨601⟩).frame sourceFrame physical.id current.global.nextPointerTag) machine) := protection
  have entered:=CurrentCallEmptyEntryControl.init_of_copy_protect options limits remaining span frames root (RootEntryFrame.raw_locals _ _ _)
    (CurrentCallPush.preparedMachine initial frames) tracker argument effect borrowFrame count source machine sourceFrame physical.id current.global.nextPointerTag place
    next sourceFn enabled sourceTracked ghost shallow sourceGhost sourceShallow fuel fuelEq sourceEq copy initial race debug stackReady rfl rfl protectedStep
  have constructorPresent : Present (ActualWorld constructor.machine) physical.id (B.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    exact ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),
      Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl)),by simp only [allocation]⟩
  have present : Present (ActualWorld machine) physical.id updated := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,{physical.entry with allocation:=updated}),Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl)),rfl⟩
  have rootTag : output.global.rootTag? physical.id=current.global.rootTag? physical.id := by rw [global];rfl
  have extra' : updated.extra=(output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed).tree := by rw [tag,global];exact extra
  obtain ⟨nextData,nextOwner,Q,pointerQ,allocationQ,completionQ,runtimeQ,owned,leaf,hidden,nodeAt,activity,parentIssued,parentBinding⟩ :=
    CurrentCallSelectedBoolWindow.window B runtime sourceFrame fresh distinct room physical.offset rfl output child actual witness tag
      constructor.machine constructorPresent rootTag machine updated present (length.trans (congrArg Allocation.len allocation))
      (bytes.trans (congrArg Allocation.byteSize allocation)) extra'
  have singleMemory : machine.memory.live=(source.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}) :=
    congrArg MemoryState.live (MemoryCopyBridge.live_update_twice source.memory physical.id
      {physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree} {physical.entry with allocation:=updated})
  have finalLive : machine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{physical.entry with allocation:=updated}) := by
    rw [singleMemory];exact MemoryCopyBridge.live_lookup_replaced source.memory physical.id _
  have finalBinding:=CurrentCallBoolWindow.replace_binding source machine physical.pointer physical.id physical.offset.toNat 1 binding physical.id physical.entry
    {physical.entry with allocation:=updated} physical.live length bytes rfl singleMemory
  have mutation' : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra updated.extra)=.ok () updated := by rw [extra];simpa only [Allocation.setExtra,Allocation.mapExtra] using mutation
  have self : updated.setExtra updated.extra=updated:=by cases updated;rfl
  obtain ⟨scalar,scalarPointer,scalarId,scalarOffset,scalarEntry,scalarBinding,scalarReady⟩:=CurrentCallEmptyEntryReturnWindow.of_mutation (final:=machine) physical updated.extra updated.extra updated mutation'
    (by rw [self];exact finalLive) rfl finalBinding ready rfl
  have resources:=CurrentCallSelectedBoolQuietSource.resources B runtime sourceFrame fresh distinct room physical.offset rfl output child actual witness tag
    constructor.machine constructorPresent rootTag
  refine ⟨output,child,machine,nextData,nextOwner,Q,?_,?_,pointerQ,(by rw [allocationQ];exact runtimeQ),?_,?_,witness.node,?_,witness.tag,leaf,hidden,?_,?_,?_,?_,?_,actual,⟨witness⟩,tag,constructor.machine,constructorPresent,rootTag,?_,?_,scalar,scalarPointer,scalarId,scalarOffset,?_,scalarBinding,scalarReady,rfl,rfl,rfl⟩
  · rw [tag];exact entered
  · rw [global];rfl
  · rw [allocationQ,extra'];exact resources.1
  · rw [allocationQ,extra'];exact resources.2
  · rw [allocationQ];exact nodeAt
  · rw [allocationQ];exact activity
  · rw [allocationQ];exact parentIssued
  · rw [allocationQ];exact parentBinding
  · rw [tag];exact returnPlace
  · rw [completionQ]
    exact S05ConcreteProtectedChildCompletion.child_edge _ _ _
  · rw [allocationQ];exact extra'
  · rw [allocationQ]
    exact singleMemory
  · rw [scalarEntry,self,allocationQ]

end
end DuplicatePrefix.CurrentCallEmptyLiveEntryCurrent

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyLiveEntryCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual empty live entry dependency {dependency}"
