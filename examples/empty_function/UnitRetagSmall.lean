import empty_function.UnitRetagResult

namespace EmptyFunction.UnitRetagSmall
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows Miri.TreeBorrows.Tree
open EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

/-- Zero-sized unresolved reborrows retain their original provenance. They
perform neither protector registration nor an allocation/tree lookup. -/
theorem reborrow_zero_unresolved {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance) (tag : BorTag)
    (state : MachineHooks.State K U)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state)
    (resolve : h.resolveAllocation place.mplace.ptr state = .ok none state)
    (log : h.logCreation = fun _ _ _ _ _ => pure ()) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag state =
      .ok place.mplace.ptr.provenance state := by
  unfold TypedRetag.reborrow
  simp only [bind,Bind.bind,EStateM.bind]
  erw [check]
  simp only [bind,Bind.bind,EStateM.bind]
  erw [resolve]
  simp [log,Size.ZERO,Size.ofBytes,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

theorem reborrow_zero_info_error {K U : Type} [DecidableEq K]
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
    (error : AllocationLookupError)
    (classification : machine.memory.getAllocInfo id = .error error) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) =
      .error (.invalidProgram ("allocation kind" ++ ": " ++ reprStr error))
        (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) := by
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
  simp [TypedRetag.checked_eq,classification,bind,Bind.bind,EStateM.bind,
    throw,throwThe,MonadExceptOf.throw,EStateM.throw,
    registeredFrame,registeredMachine,registeredTracker,withCurrent]
  constructor <;> rfl

open Lean Elab Command in
run_cmd do
  for name in #[``reborrow_zero_unresolved,``reborrow_zero_info_error] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved small zero-retag axiom {dependency} in {name}"
end EmptyFunction.UnitRetagSmall
