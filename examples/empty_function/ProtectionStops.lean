import empty_function.LiveProtectionOutcome
import empty_function.ResourceFailures

namespace EmptyFunction.ProtectionStops
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
open EmptyFunction.ProtectionOutcome EmptyFunction.LiveProtectionOutcome EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-- Entry-tag exhaustion is preserved as its actual checked invariant stop. -/
theorem maximum (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState)
    (layout : place.layout = s.abi.ret.layout)
    (enabled : before.borrowTracker = some tracker)
    (maximum : tracker.global.nextPointerTag.value = 18446744073709551615) :
    Outcome s place frames frame before := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  obtain ⟨reason,actual⟩ := ResourceFailures.protect_maximum_failure s.cfg.retag s.limits.retag place
    (LocalUnit.current frames frame before) tracker _ (fields.size place layout) enabled maximum
  exact Or.inl ⟨.invalidProgram reason,LocalUnit.current frames frame before,actual,rfl⟩

private theorem reborrow_ensure_error {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (info : AllocationInfo)
    (classified : machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (error : StepError) (failedState : MachineHooks.State K U)
    (failed : h.ensureTreeExtra id
      (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) =
      .error error failedState) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) = .error error failedState := by
  let start := withCurrent frames frame machine
  have current : MachineHooks.currentFrame start = .ok frame start := by
    simp [MachineHooks.currentFrame, Stack.currentFrame?, start, withCurrent,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  unfold TypedRetag.reborrow
  simp only [check,resolve,log,bind,EStateM.bind,pure,EStateM.pure,MachineHooks.protectionPolicy]
  rw [current]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply]
  simp only [start,withCurrent,enabled,bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,EStateM.set,Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  simp only [TypedRetag.checked_eq,classified,bind,EStateM.bind,pure,EStateM.pure]
  simp only [data,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  erw [TypedRetag.insidePermissions_unit h budget place precise freeze]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [failed]

theorem ensure_error (s : Static) (metadata : Metadata s) (profile : Profile s)
    (place : MPlaceTy Provenance) (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (before : Machine) (tracker : MachineHooks.BorrowState) (global : GlobalState) (tag : BorTag)
    (layout : place.layout = s.abi.ret.layout)
    (enabled : before.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (tagged : tracker.global.newPointerTag = .ok (global,tag))
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra)
    (resolve : s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (taggedMachine before tracker global)) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (LocalUnit.current frames frame (taggedMachine before tracker global)))
    (info : AllocationInfo) (classification : before.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (error : StepError) (failedState : State)
    (failed : s.cfg.retag.ensureTreeExtra id
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tag)
        (UnitRetag.registeredMachine (taggedMachine before tracker global) {tracker with global} tag)) =
      .error error failedState)
    (safe : RunLoop.reportsUB error = false) : Outcome s place frames frame before := by
  have fields := CanonicalUnitRetag.fields s metadata profile
  have tagEnabled : (taggedMachine before tracker global).borrowTracker = some {tracker with global} := rfl
  have borrowed := reborrow_ensure_error s.cfg.retag s.limits.retag place
    frames frame {} (taggedMachine before tracker global) {tracker with global} tagEnabled frameBorrow
    id offset parent tag (fields.check _ _) resolve fields.log fields.precise
    (fields.freeze place layout) info classification data error failedState failed
  apply Or.inl
  refine ⟨error,failedState,?_,safe⟩
  exact UnitRetagResult.protect_of_failed_reborrow s.cfg.retag s.limits.retag place
    (LocalUnit.current frames frame before) tracker global tag (fields.size place layout)
    enabled tagged error failedState borrowed

open Lean Elab Command in
run_cmd do
  for name in #[``maximum,``ensure_error] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved actual protection stop axiom {dependency} in {name}"
#print axioms ensure_error
end EmptyFunction.ProtectionStops
