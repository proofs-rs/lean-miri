import empty_function.InitializationPrefix
import empty_function.UnitRetag
namespace EmptyFunction.ProtectionOutcome
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
abbrev Machine := MachineHooks.MachineState MiriMemoryKind Configuration.RootUser

/-- Only the state projections needed by the fixed unit body and terminator.
Allocation storage, counters, root caches and the actual choice tape can change. -/
structure Stable (before after : Machine) : Prop where
  threads : after.threads = before.threads
  noRace : after.dataRace = before.dataRace
  ghost : after.user.payload.ghost = before.user.payload.ghost
  validation : after.user.payload.validation = before.user.payload.validation
  control : after.user.payload.payload.user.host.control = before.user.payload.payload.user.host.control

/-- Certificates for the actual frame-exit operation. This is a derived
postcondition of protection, never a validity or resource admission field. -/
inductive ReleaseReady (machine : Machine) (borrow : FrameState) : Prop where
  | empty (tracker : MachineHooks.BorrowState)
      (enabled : machine.borrowTracker = some tracker) (frame : borrow = {})
  | nondata (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
      (info : AllocationInfo) (enabled : machine.borrowTracker = some tracker)
      (frame : borrow = ({} : FrameState).addProtector id tag)
      (metadata : machine.memory.getAllocInfo id = .ok info) (kind : info.kind ≠ .liveData)
  | live (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
      (entry : InputDraft.Entry) (enabled : machine.borrowTracker = some tracker)
      (frame : borrow = ({} : FrameState).addProtector id tag)
      (lookup : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (released : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags =
        ⟨entry.allocation.extra,.Released⟩)

/-- A pointwise outcome of the actual unit protection operation. Safe failures
retain their actual failed state. Success preserves the frame except for its
owned-protector record and supplies the exact exit certificate. This proposition
is an internal implementation goal and is not part of CurrentInput or Target. -/
def Outcome (s : Static) (place : MPlaceTy Provenance) (frames : Array LocalUnit.F)
    (frame : LocalUnit.F) (before : Machine) : Prop :=
  (∃ error failed,
    TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) = .error error failed ∧
    RunLoop.reportsUB error = false) ∨
  (∃ (borrow : FrameState) (after : Machine),
    TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) =
      .ok () (LocalUnit.current frames {frame with extra := {frame.extra with borrowTracker := some borrow}} after) ∧
    Stable before after ∧ ReleaseReady after borrow)

end EmptyFunction.ProtectionOutcome
