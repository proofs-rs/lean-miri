import empty_function.ProtectionSmallTotal
namespace EmptyFunction.SmallProtectionSnapshot
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.ProtectionSmallTotal
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem unresolved (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout) (noMeta : place.mplace.metadata = .none)
    (aligned : place.mplace.misaligned = none)
    (resolve : ∀ global, s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (allocatedMachine before tracker global)) =
      .ok none (LocalUnit.current frames frame (allocatedMachine before tracker global)))
    (afterState : State)
    (success : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) = .ok () afterState) :
    afterState.machine.memory = before.memory ∧
      afterState.machine.user.addresses = before.user.addresses := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  rcases ResourceFailures.tag_total tracker.global with ⟨maximum,failed⟩ |
      ⟨global,tagged,room,counter,roots,protectors,tracked⟩
  · obtain ⟨reason,actual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker (some (Size.ZERO,Align.ONE))
      (fields.size place layout) enabled maximum
    rw [success] at actual
    cases actual
  · let after := allocatedMachine before tracker global
    let state := LocalUnit.current frames frame before
    let next := LocalUnit.current frames frame after
    have borrowed := UnitRetagSmall.reborrow_zero_unresolved s.cfg.retag s.limits.retag place
      tracker.global.nextPointerTag next (fields.check _ _) (resolve global) fields.log
    have actual := UnitRetagResult.protect_of_returned_reborrow s.cfg.retag s.limits.retag place
      state tracker global tracker.global.nextPointerTag (fields.size place layout) enabled tagged
      place.mplace.ptr.provenance next next borrowed (fun present => present)
      (fields.write place place.mplace.ptr.provenance layout noMeta aligned next)
    have same : afterState = next := by
      have equation := success.symm.trans actual
      injection equation
    rw [same]
    exact ⟨rfl,rfl⟩

theorem resolved_nondata (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout) (noMeta : place.mplace.metadata = .none)
    (aligned : place.mplace.misaligned = none)
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra)
    (resolve : ∀ global, s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (allocatedMachine before tracker global)) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (LocalUnit.current frames frame (allocatedMachine before tracker global)))
    (info : AllocationInfo) (classification : before.memory.getAllocInfo id = .ok info)
    (nondata : info.kind ≠ .liveData)
    (afterState : State)
    (success : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) = .ok () afterState) :
    afterState.machine.memory = before.memory ∧
      afterState.machine.user.addresses = before.user.addresses := by
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
    let after := UnitRetag.registeredMachine entered enteredTracker tracker.global.nextPointerTag
    let afterFrame := UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag
    let state := LocalUnit.current frames frame before
    let next := LocalUnit.current frames afterFrame after
    have borrowed := UnitRetag.reborrow_zero_nondata_from_equations s.cfg.retag s.limits.retag place
      frames frame {} entered enteredTracker rfl frameBorrow id offset parent tracker.global.nextPointerTag
      (fields.check _ _) (resolve global) fields.log info classification nondata
    have actual := UnitRetagResult.protect_of_returned_reborrow s.cfg.retag s.limits.retag place
      state tracker global tracker.global.nextPointerTag (fields.size place layout) enabled tagged
      (some (.concrete id tracker.global.nextPointerTag)) next next borrowed (by simp)
      (fields.write place _ layout noMeta aligned next)
    have same : afterState = next := by
      have equation := success.symm.trans actual
      injection equation
    rw [same]
    exact ⟨rfl,rfl⟩

open Lean Elab Command in
run_cmd do
  for name in #[``unresolved,``resolved_nondata] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved small snapshot axiom {dependency}"
#print axioms unresolved
#print axioms resolved_nondata
end EmptyFunction.SmallProtectionSnapshot
