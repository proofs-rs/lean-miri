import empty_function.SmallProtectionSnapshot
namespace EmptyFunction.ProtectionInfoError
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.ProtectionSmallTotal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem info_error_impossible (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout)
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra)
    (resolve : ∀ global, s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (allocatedMachine before tracker global)) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (LocalUnit.current frames frame (allocatedMachine before tracker global)))
    (error : AllocationLookupError) (classification : before.memory.getAllocInfo id = .error error)
    (afterState : State)
    (success : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) = .ok () afterState) : False := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  rcases ResourceFailures.tag_total tracker.global with ⟨maximum,failed⟩ |
      ⟨global,tagged,room,counter,roots,protectors,tracked⟩
  · obtain ⟨reason,actual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker (some (Size.ZERO,Align.ONE))
      (fields.size place layout) enabled maximum
    rw [success] at actual
    cases actual
  · let entered := allocatedMachine before tracker global
    let enteredTracker : MachineHooks.BorrowState := {tracker with global}
    have borrowed := UnitRetagSmall.reborrow_zero_info_error s.cfg.retag s.limits.retag place frames frame {}
      entered enteredTracker rfl frameBorrow id offset parent tracker.global.nextPointerTag
      (fields.check _ _) (resolve global) fields.log error classification
    have actual := UnitRetagResult.protect_of_failed_reborrow s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker global tracker.global.nextPointerTag
      (fields.size place layout) enabled tagged _ _ borrowed
    rw [success] at actual
    cases actual

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``info_error_impossible) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved allocation-info stop axiom {dependency}"
#print axioms info_error_impossible
end EmptyFunction.ProtectionInfoError
