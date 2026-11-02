import duplicate_prefix.CurrentCallBoolProtection
namespace DuplicatePrefix.CurrentCallBoolActivation
open Miri.DataStructures
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Plain actual tree certificates compose into destination protection. The
fresh pointer is used only by writeUninit; the frame retains its original destination. -/
theorem protect_of_steps (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker=some tracker) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none)
    (backend : machine.user.payload.payload.user.backend=.none)
    (parentTree childTree : BorrowTree)
    (readTree : (physical.entry.allocation.extra.performBorrowAccessRange
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree=parentTree)
    (readDone : (physical.entry.allocation.extra.performBorrowAccessRange
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed)
    (child : parentTree.newChild (Size.ofBytes physical.offset) (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome=⟨childTree,.ok ()⟩)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (writeDone : (childTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed) :
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry childTree
    let written := childTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra childTree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace := by
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry childTree
  let childWindow := CurrentCallBoolWindow.protected_window physical frames frame borrowFrame tracker fresh childTree
  have retag := CurrentCallBoolProtection.retag_of_steps options remaining span ctx limits.retag machine tracker frames frame borrowFrame
    enabled frameBorrow place physical.layout physical.pointer physical.physicalPointer physical.id physical.offset.toNat binding physical.entry physical.live
    fresh race parentTree childTree (by simpa using readTree) (by simpa using readDone) (by simpa using child)
  obtain ⟨sync,extras,outside⟩ := ready
  obtain ⟨updated,write,extra,bytes,length,mutable,mutation⟩ := CurrentCallBoolProtection.write_uninit_concrete options remaining span ctx retagged
    (TypedRetagGeneric.retaggedPlace place physical.id tracker.global.nextPointerTag) childWindow
    (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) rfl tracker.global.nextPointerTag rfl ghost race backend
    sync extras outside (by exact writeDone)
  refine ⟨updated,?_,extra,bytes,length,mutable,mutation,?_,rfl,rfl,rfl⟩
  · change TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag limits.retag place (Storage.withCurrent frames frame machine)=_
    unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,enabled,Option.isSome_some,ite_true]
    erw [retag]
    exact write
  · have snapshot := CurrentCallBoolProtection.uninit_snapshot _ updated _ _ mutation
    exact snapshot

end
end DuplicatePrefix.CurrentCallBoolActivation
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallBoolActivation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved Bool activation dependency {dependency}"
