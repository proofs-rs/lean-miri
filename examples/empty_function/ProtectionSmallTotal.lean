import empty_function.ProtectionOutcome
import empty_function.CanonicalUnitRetag
import empty_function.UnitRetagSmall
import empty_function.ResourceFailures

/-! Actual unit protection outcomes for unresolved and non-data pointers.
Resolved-query equalities are internal canonical-preflight composition edges. -/
namespace EmptyFunction.ProtectionSmallTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
abbrev Machine := ProtectionOutcome.Machine

def allocatedMachine (before : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState) : Machine :=
  {before with borrowTracker := some {tracker with global}}

theorem allocated_stable (before : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState) :
    ProtectionOutcome.Stable before (allocatedMachine before tracker global) := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem unresolved (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout) (noMeta : place.mplace.metadata = .none)
    (aligned : place.mplace.misaligned = none)
    (resolve : ∀ global, s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (allocatedMachine before tracker global)) =
      .ok none (LocalUnit.current frames frame (allocatedMachine before tracker global))) :
    ProtectionOutcome.Outcome s place frames frame before := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  rcases ResourceFailures.tag_total tracker.global with ⟨maximum,failed⟩ |
      ⟨global,tagged,room,counter,roots,protectors,tracked⟩
  · obtain ⟨reason,actual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker (some (Size.ZERO,Align.ONE))
      (fields.size place layout) enabled maximum
    exact Or.inl ⟨.invalidProgram reason,_,actual,rfl⟩
  · let after := allocatedMachine before tracker global
    let state := LocalUnit.current frames frame before
    let next := LocalUnit.current frames frame after
    have borrowed := UnitRetagSmall.reborrow_zero_unresolved s.cfg.retag s.limits.retag place
      tracker.global.nextPointerTag next (fields.check _ _) (resolve global) fields.log
    have actual := UnitRetagResult.protect_of_returned_reborrow s.cfg.retag s.limits.retag place
      state tracker global tracker.global.nextPointerTag (fields.size place layout) enabled tagged
      place.mplace.ptr.provenance next next borrowed (fun present => present)
      (fields.write place place.mplace.ptr.provenance layout noMeta aligned next)
    have sameFrame : {frame with extra := {frame.extra with borrowTracker := some {}}} = frame := by
      rw [←frameBorrow]
    right
    refine ⟨{},after,?_,allocated_stable before tracker global,?_⟩
    · simpa only [sameFrame] using actual
    · exact .empty {tracker with global} rfl rfl

/-- Absent provenance derives its canonical unresolved query directly. -/
theorem integer (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout) (noMeta : place.mplace.metadata = .none)
    (aligned : place.mplace.misaligned = none) (provenance : place.mplace.ptr.provenance = none) :
    ProtectionOutcome.Outcome s place frames frame before := by
  apply unresolved s metadata profile place frames frame before tracker enabled frameBorrow layout noMeta aligned
  intro global
  rw [(ConcreteProtection.bindings s metadata (BodyTotal.capacity_positive s)).1]
  exact UnitProtection.resolve_integer (ConcreteProtection.source s).pointers place.mplace.ptr provenance _

/-- The non-data branch registers its actual singleton protector and performs
no materialization or tree access. No tag room is assumed. -/
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
    (nondata : info.kind ≠ .liveData) :
    ProtectionOutcome.Outcome s place frames frame before := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  rcases ResourceFailures.tag_total tracker.global with ⟨maximum,failed⟩ |
      ⟨global,tagged,room,counter,roots,protectors,tracked⟩
  · obtain ⟨reason,actual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker (some (Size.ZERO,Align.ONE))
      (fields.size place layout) enabled maximum
    exact Or.inl ⟨.invalidProgram reason,_,actual,rfl⟩
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
    right
    refine ⟨({} : FrameState).addProtector id tracker.global.nextPointerTag,after,actual,?_,?_⟩
    · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    · exact .nondata (UnitRetag.registeredTracker enteredTracker tracker.global.nextPointerTag)
        id tracker.global.nextPointerTag info rfl rfl classification nondata

/-- Concrete non-data pointers discharge their resolver from raw pointer/base
rows and the selected target width; no query-success premise is exposed. -/
theorem nondata_concrete (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout) (noMeta : place.mplace.metadata = .none)
    (aligned : place.mplace.misaligned = none)
    (id : AllocId) (parent : BorTag) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parent)) (Size.ofBytes address))
    (cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo) (classification : before.memory.getAllocInfo id = .ok info)
    (nondata : info.kind ≠ .liveData) :
    ProtectionOutcome.Outcome s place frames frame before := by
  apply resolved_nondata s metadata profile place frames frame before tracker enabled frameBorrow layout noMeta aligned
    id (address-base) (.concrete parent) ?_ info classification nondata
  intro global
  rw [(ConcreteProtection.bindings s metadata (BodyTotal.capacity_positive s)).1,encoding]
  exact UnitProtection.resolve_concrete (ConcreteProtection.source s).pointers id parent address base
    (ConcreteProtection.source_truncate s metadata.pointerSize) _ cached

/-- A failed pure allocation-info query is an observed invariant stop after
protector registration. The partially updated state is not rolled back. -/
theorem resolved_info_error (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some {})
    (layout : place.layout = s.abi.ret.layout)
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra)
    (resolve : ∀ global, s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (allocatedMachine before tracker global)) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (LocalUnit.current frames frame (allocatedMachine before tracker global)))
    (error : AllocationLookupError) (classification : before.memory.getAllocInfo id = .error error) :
    ProtectionOutcome.Outcome s place frames frame before := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  rcases ResourceFailures.tag_total tracker.global with ⟨maximum,failed⟩ |
      ⟨global,tagged,room,counter,roots,protectors,tracked⟩
  · obtain ⟨reason,actual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker (some (Size.ZERO,Align.ONE))
      (fields.size place layout) enabled maximum
    exact Or.inl ⟨.invalidProgram reason,_,actual,rfl⟩
  · let entered := allocatedMachine before tracker global
    let enteredTracker : MachineHooks.BorrowState := {tracker with global}
    have borrowed := UnitRetagSmall.reborrow_zero_info_error s.cfg.retag s.limits.retag place frames frame {}
      entered enteredTracker rfl frameBorrow id offset parent tracker.global.nextPointerTag
      (fields.check _ _) (resolve global) fields.log error classification
    have actual := UnitRetagResult.protect_of_failed_reborrow s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) tracker global tracker.global.nextPointerTag
      (fields.size place layout) enabled tagged _ _ borrowed
    exact Or.inl ⟨_,_,actual,rfl⟩

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ProtectionSmallTotal.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved small protection total axiom {dependency} in {name}"
  logInfo m!"Audited {count} small protection total declarations"
end EmptyFunction.ProtectionSmallTotal
