import duplicate_prefix.S04ReturnProtectionResources
import duplicate_prefix.S04ReturnRetaggedInput

namespace DuplicatePrefix.S04ReturnProtectionInput
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open Miri.Input DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Execute the general concrete return protection and form its actual next
write's raw Input on the returned machine state. All byte/address metadata is
transported from the original input; the child capability is derived by the
real retag. There is no future Input or successful operation in the premises. -/
theorem invoke_concrete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (len : UInt64)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    ∃ (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree),
      TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame before) =
        .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
          (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree) ∧
      ∃ next : DuplicatePrefixReturnPlaceInput.Input
        (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree).machine
        (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag),
        next.id = input.id ∧ next.offset = input.offset ∧ next.capacity = input.capacity ∧
        next.entry.allocation.extra = tree ∧
        DuplicatePrefixBorrowContract.RuntimeFacts tree next.tracker.global ∧
        tree.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 := by
  obtain ⟨fresh,tree,actual,runtime,capacity,growth,child,selected,selectedEq,tagged,⟨positive⟩⟩ :=
    S04ReturnProtectionResources.invoke_concrete budget before tracker model place len input state resources
      tag concrete frames frame borrowFrame frameBorrow
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame borrowFrame fresh tree child
    (some selected) input.maximum tagged capacity positive
  exact ⟨fresh,tree,actual,next,rfl,rfl,rfl,rfl,runtime,growth⟩

end DuplicatePrefix.S04ReturnProtectionInput
