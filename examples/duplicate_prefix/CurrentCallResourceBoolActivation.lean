import duplicate_prefix.CurrentCallResourceChildWrite
import duplicate_prefix.CurrentCallResourceSourceKeyOrigin
import duplicate_prefix.CurrentCallSourceInstallState
import duplicate_prefix.CurrentCallBoolActivationOperation
namespace DuplicatePrefix.CurrentCallResourceBoolActivation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- A return-role resource derives both actual Bool retagging and its concrete-child activation. -/
theorem activate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (data : Identities) (owner : Nat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (W : UniformWindow machine tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=W.pointer.value) (allocation : physical.entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : W.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace := by
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live)
  have distinct : W.allocation.extra.roots.toList.Nodup := by rw [←allocation];exact state.roots (physical.id,physical.entry) member
  have bounds : physical.offset.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have length := state.treeLength (physical.id,physical.entry) member
    rw [allocation] at length
    rw [length,←allocation,physical.size]
    exact physical.bounds
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  have oldShort : W.allocation.extra.nodes.size<65536 := by omega
  obtain ⟨output,child,actual,tag,global,frameEq,readDone,childDone,lookup,⟨witness⟩⟩ := CurrentCallResourceFnEntry.correlated_borrow W runtime state highwater borrowFrame fresh
    (by rfl) distinct oldShort nodeRoom physical.offset 1 rfl rfl (by decide) bounds
  have keys := CurrentCallResourceSourceKeyOrigin.operation W runtime state highwater borrowFrame fresh (by rfl) distinct oldShort nodeRoom
    physical.offset 1 rfl rfl (by decide) bounds output actual
  have afterDistinct := CurrentCallResourceSourceKeyOrigin.roots W runtime state highwater borrowFrame fresh (by rfl) distinct oldShort nodeRoom
    physical.offset 1 rfl rfl (by decide) bounds output actual
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  have enabled : retagged.machine.borrowTracker=some next := by
    change retagged.machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩
    rw [global]
    rfl
  have capacity : output.child.tree.locations.size=physical.entry.allocation.extra.locations.size := by rw [allocation];exact witness.capacity
  have keyOrigin : ∀ key index,(key,index)∈output.child.tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨∃old,(key,old)∈physical.entry.allocation.extra.tagMapping.mapping := by
    rw [allocation];exact keys
  obtain ⟨postState,postHighwater⟩ := CurrentCallSourceInstallState.install machine retagged.machine tracker next state highwater physical.id physical.entry physical.live
    borrowFrame fresh global output.child.tree witness.runtime afterDistinct capacity keyOrigin enabled rfl
  have present : Present (ActualWorld retagged.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),?_,?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (MemoryCopyBridge.live_lookup_replaced machine.memory physical.id _))
    · simp only [allocation]
  have rootTag : output.global.rootTag? physical.id=tracker.global.rootTag? physical.id := by rw [global];rfl
  have actualRealized := CandidateCurrentGrantRuntime.actual_state retagged.machine next postState
  have growth : output.child.tree.nodes.size≤W.allocation.extra.nodes.size+1 := by
    have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1 := by
      exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ fresh _ _ _))
    obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global borrowFrame physical.id fresh runtime
    let registration := registered tracker.global borrowFrame physical.id fresh
    let accessed := output.access
    obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read W runtime state highwater borrowFrame fresh (by rfl)
      distinct oldShort physical.offset 1 rfl rfl bounds
    change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree registration.1 at afterRuntime
    rw [←literalEq] at afterRuntime
    change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree.nodes=W.allocation.extra.nodes at nodes
    change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
    change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree.locations.size=W.allocation.extra.locations.size at bytes
    rw [←literalEq] at nodes tags bytes
    have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
    have room : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
    have childBounds : physical.offset.toNat+1≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
    have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
      have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
      change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
      omega
    have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
    have childEq : output.child=output.access.tree.newChild (Size.ofBytes physical.offset) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
    cases prov : W.pointer.value.provenance with
    | concrete id parentTag =>
      obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
      rw [prov] at binds
      have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
      have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
      have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
        tagged parentAfter freshAfter room tagBound tagHeld physical.offset 1 (by decide) childBounds
      rw [childEq]
      simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2
    | wildcard =>
      have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter room tagBound tagHeld
        physical.offset 1 (by decide) childBounds
      rw [childEq]
      simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2.1
  have afterShort : output.child.tree.nodes.size<65536 := by omega
  have afterBounds : physical.offset.toNat+1≤output.child.tree.locations.size.bytes.toNat := by rw [witness.capacity];exact bounds
  have writeDone := CurrentCallResourceChildWrite.child_write W runtime output child physical.offset 1 witness tag retagged.machine present rootTag actualRealized
    afterDistinct afterShort rfl rfl afterBounds .VisitChildrenOfAccessed
  have actualPhysical : CandidateCurrentFnEntryRaw.operation physical.entry.allocation.extra tracker.global borrowFrame physical.id physical.pointer.provenance physical.offset 1=.ok output := by
    rw [allocation,pointer];exact actual
  have writePhysical : (output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
    rw [tag,global] at writeDone
    exact writeDone
  refine ⟨output,child,actual,tag,global,frameEq,⟨witness⟩,?_⟩
  exact CurrentCallBoolActivation.protect_of_operation options limits remaining span ctx machine tracker frames frame borrowFrame state.enabled frameBorrow
    place physical binding fresh ghost race backend output actualPhysical readDone childDone ready writePhysical

end
end DuplicatePrefix.CurrentCallResourceBoolActivation
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceBoolActivation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource Bool activation dependency {dependency}"
