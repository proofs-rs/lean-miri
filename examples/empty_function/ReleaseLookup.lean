import empty_function.UnitRetagResult

namespace EmptyFunction.ReleaseLookup
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Actual singleton release from arbitrary live-array order. Even an unchanged
allocation is written through filter/push; that normalization is kept in the post. -/
theorem live {K U : Type} [DecidableEq K]
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tag : BorTag)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (released : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags =
      ⟨entry.allocation.extra,.Released⟩) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure kind globals)
      (withCurrent frames (registeredFrame frame {} id tag) machine) =
      .ok () (withCurrent frames (registeredFrame frame {} id tag)
        {machine with memory := replaceTree machine.memory id entry entry.allocation.extra, borrowTracker := some {tracker with global := tracker.global.endCall (({} : FrameState).addProtector id tag)}}) := by
  let state := withCurrent frames (registeredFrame frame {} id tag) machine
  have info : machine.memory.getAllocInfo id =
      .ok ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo,live]
    rfl
  have ensure := EmptyFunction.UnitProtection.ensure_live kind globals synchronize state id entry live
  have mutation := set_live machine.memory id entry entry.allocation.extra live
  dsimp only [state,withCurrent,registeredFrame,FrameState.addProtector] at ensure
  unfold MachineHooks.beforeStackPopWithEnsure
  simp [get,getThe,MonadStateOf.get,EStateM.get,withCurrent,
    MachineHooks.currentFrame,Stack.currentFrame?,registeredFrame,FrameState.addProtector,enabled,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,info]
  erw [ensure]
  simp [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    withCurrent,registeredFrame,live,enabled]
  erw [released]
  simp only [Allocation.setExtra,Allocation.mapExtra] at mutation
  erw [mutation]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set,GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  simp only [enabled,bind,Bind.bind,EStateM.bind,set,EStateM.set]
  rfl

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``live) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual release lookup axiom {dependency}"
#print axioms live
end EmptyFunction.ReleaseLookup
