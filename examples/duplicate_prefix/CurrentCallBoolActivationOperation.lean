import duplicate_prefix.CurrentCallBoolActivation
import duplicate_prefix.CurrentCallTypedFnEntry
namespace DuplicatePrefix.CurrentCallBoolActivation
open Miri.DataStructures
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open CurrentCallTypedFnEntry GeneralBorrowFnEntryRegistration
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual FnEntry operation normalizes to the exact Read and child certificates
consumed by Bool protection. The original frame destination remains unchanged. -/
theorem protect_of_operation (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker=some tracker) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none)
    (backend : machine.user.payload.payload.user.backend=.none)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation physical.entry.allocation.extra tracker.global borrowFrame
      physical.id physical.pointer.provenance physical.offset 1 = .ok output)
    (readCompleted : output.access.status = .Completed)
    (childCompleted : output.child.outcome = .ok ())
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (writeDone : (output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status=.Completed) :
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
  have literalEq : output = literal physical.entry.allocation.extra tracker.global borrowFrame physical.id fresh
      physical.pointer.provenance physical.offset 1 := by
    apply Except.ok.inj
    exact actual.symm.trans (literal_operation _ _ _ _ fresh _ _ _)
  have readDone := readCompleted
  have childDone := childCompleted
  rw [literalEq] at readDone childDone
  let accessed := physical.entry.allocation.extra.performBorrowAccessRange
    (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) .Read
    (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  have childEq : accessed.tree.newChild (Size.ofBytes physical.offset)
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome =
      ⟨output.child.tree,.ok ()⟩ := by
    rw [literalEq]
    change (literal physical.entry.allocation.extra tracker.global borrowFrame physical.id fresh physical.pointer.provenance physical.offset 1).child = ⟨(literal physical.entry.allocation.extra tracker.global borrowFrame physical.id fresh physical.pointer.provenance physical.offset 1).child.tree,.ok ()⟩
    cases found : (literal physical.entry.allocation.extra tracker.global borrowFrame physical.id fresh
        physical.pointer.provenance physical.offset 1).child with
    | mk final outcome =>
      rw [found] at childDone
      cases childDone
      rfl
  exact protect_of_steps options limits remaining span ctx machine tracker frames frame borrowFrame enabled frameBorrow
    place physical binding fresh ghost race backend accessed.tree output.child.tree rfl
    (by simpa only [literal,accessed,registered,GeneralBorrowFnEntryRegistration.advanced,allocatedTracker,
      registeredGlobal,GlobalState.addProtector,ite_true] using readDone)
    childEq ready writeDone

end
end DuplicatePrefix.CurrentCallBoolActivation
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallBoolActivation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved Bool activation dependency {dependency}"
