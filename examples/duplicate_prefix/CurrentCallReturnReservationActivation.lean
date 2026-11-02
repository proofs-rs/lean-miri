import duplicate_prefix.CurrentCallReturnReservationShift
import duplicate_prefix.CurrentCallBoolActivation

/-! Attach scoped resource bookkeeping to the EXACT output shape of actual
Bool protection. The operation equation is consumed from protect_of_steps;
this adapter neither proves a new access nor restores the original grant. -/
namespace DuplicatePrefix.CurrentCallReturnReservationActivation
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CandidateFreezeContentResources CurrentCallReturnReservation CurrentCallReturnReservationShift CurrentCallOwnerRenaming
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The memory-only final update in BoolActivation.protect_of_steps. It leaves
the captured fresh protector and original frame destination unchanged. -/
def output {machine : Before} {place : MPlaceTy Provenance}
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (childTree : BorrowTree) (updated : Allocation Provenance BorrowTree) : RootState :=
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry childTree
  {retagged with machine := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter (fun row => row.1 != physical.id)).push
      (physical.id,{physical.entry with allocation := updated}))}}}

/-- The exact actual protector, table entry, one-byte footprint, and retained
ORIGINAL returnPlace travel with the internally fresh reservation. No initialized
Bool value, ret delegation, finite owner support, or original-grant access is
an input. The operational equality comes from the actual Bool producer. -/
theorem attach (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : Before) (place : MPlaceTy Provenance)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (childTree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (operationDone : (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine) =
      .ok () (output physical frames frame borrowFrame tracker fresh childTree updated))
    (F : Fragment) (valid : Valid F) (original : Owner)
    (owned : ∀ byte, Window physical.id physical.offset.toNat 1 byte →
      F byte original = some ⟨.ret,.active⟩) :
    ∃ reservation : Scope (RuntimeStackPlace Provenance × MPlaceTy Provenance),
      reservation.originalDestination = (frame.returnPlace,place) ∧
      reservation.originalOwner = original + 1 ∧ reservation.temporaryOwner = 0 ∧
      reservation.window = Window physical.id physical.offset.toNat 1 ∧
      reservation.before = shiftContent F ∧
      Valid (begin (shiftContent F) (original + 1) 0 (Window physical.id physical.offset.toNat 1)) ∧
      (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
        (Storage.withCurrent frames frame machine) =
        .ok () (output physical frames frame borrowFrame tracker fresh childTree updated) ∧
      (output physical frames frame borrowFrame tracker fresh childTree updated).machine.borrowTracker =
        some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (output physical frames frame borrowFrame tracker fresh childTree updated).stack.frames =
        frames.push (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag) ∧
      (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags.get
        tracker.global.nextPointerTag = some .StrongProtector ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker =
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (physical.id,tracker.global.nextPointerTag) ∈
        (borrowFrame.addProtector physical.id tracker.global.nextPointerTag).protectedTags ∧
      (TypedRetagGeneric.retaggedPlace place physical.id tracker.global.nextPointerTag).mplace.ptr.provenance =
        some (.concrete physical.id tracker.global.nextPointerTag) ∧
      (TypedRetagGeneric.retaggedPlace place physical.id tracker.global.nextPointerTag).mplace.ptr.offset =
        physical.pointer.offset ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace =
        reservation.originalDestination.1 := by
  classical
  refine ⟨scope (frame.returnPlace,place) F original (Window physical.id physical.offset.toNat 1) owned,
    rfl,rfl,rfl,rfl,rfl,begin_valid_shifted F valid original _,operationDone,rfl,rfl,?_,rfl,?_,rfl,?_,rfl⟩
  · exact ProtectedTags.get_insert_same _ _ _
  · simp [FrameState.addProtector]
  · change place.mplace.ptr.offset = physical.pointer.offset
    rw [physical.physicalPointer]
    rfl

end
end DuplicatePrefix.CurrentCallReturnReservationActivation
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallReturnReservationActivation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved activation reservation dependency {dependency}"
