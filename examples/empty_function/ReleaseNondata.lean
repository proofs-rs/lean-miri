import empty_function.UnitRetag

namespace EmptyFunction.ReleaseNondata
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- A singleton non-data protector skips ensure/tree access and only executes
the current global end_call bookkeeping. No original-map freshness is assumed. -/
theorem nondata {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit)
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (id : AllocId) (tag : BorTag)
    (info : AllocationInfo) (classification : machine.memory.getAllocInfo id = .ok info)
    (nondata : info.kind ≠ .liveData) :
    MachineHooks.beforeStackPopWithEnsure ensure
      (withCurrent frames (registeredFrame frame {} id tag) machine) =
      .ok () (withCurrent frames (registeredFrame frame {} id tag)
        {machine with borrowTracker := some {tracker with
          global := tracker.global.endCall (({} : FrameState).addProtector id tag)}}) := by
  simp [MachineHooks.beforeStackPopWithEnsure,withCurrent,registeredFrame,enabled,
    MachineHooks.currentFrame,Stack.currentFrame?,FrameState.addProtector,classification,nondata,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set,GlobalState.endCall,←Array.foldl_toList,List.foldl_cons,List.foldl_nil]

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``nondata) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved current non-data release axiom {dependency}"
#print axioms nondata
end EmptyFunction.ReleaseNondata
