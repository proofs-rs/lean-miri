import duplicate_prefix.S02SeparateDestinationSharedFrame

namespace DuplicatePrefix.S02ConcreteReferenceIdentity
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Independently chosen Positive witnesses for the same concrete slice agree
on the physical source pointer and the borrow tracker's fresh argument tag.
This aligns the call-entry and source-tree packets without choosing a history. -/
theorem current_pointer_same
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (left right : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address)) len) :
    Pointer.new (Provenance.concrete left.id left.tracker.global.nextPointerTag)
      (Size.ofBytes (left.base+left.offset)) =
    Pointer.new (Provenance.concrete right.id right.tracker.global.nextPointerTag)
      (Size.ofBytes (right.base+right.offset)) := by
  have leftBinding := left.binding
  have rightBinding := right.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at leftBinding rightBinding
  have ids : left.id = right.id := leftBinding.1.symm.trans rightBinding.1
  have trackers : left.tracker = right.tracker :=
    Option.some.inj (left.enabled.symm.trans right.enabled)
  have addresses : left.base+left.offset = right.base+right.offset :=
    left.pointerAddress.symm.trans right.pointerAddress
  rw [ids,trackers,addresses]

end
end DuplicatePrefix.S02ConcreteReferenceIdentity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteReferenceIdentity.current_pointer_same) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete reference identity dependency {dependency}"
