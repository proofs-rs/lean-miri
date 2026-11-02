import duplicate_prefix.GlobalDataOnlyConversion

/-! The real global allocation-extra initialization, with race checking off and
an existing stable per-allocation root tag. Allocation mutability is not an
input to this operation. The initial in-bounds permission is Unique/accessed;
out-of-bounds defaults remain Disabled and the root is not exposed. -/
namespace DuplicatePrefix.GlobalDataOnlyExtra
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem init_extra {K U P : Type} [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P)
    (before : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (size : Size) (align : Align)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == id)) = false) :
    GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align before =
      .ok (BorrowTree.new root size) (MemoryExtras.putAllocation extras before id ⟨none,#[]⟩) := by
  have rootEq := GlobalState.rootPointerTag_existing tracker.global id root rootCached
  have unchanged : {before with borrowTracker := some tracker} = before := by rw [←enabled]
  simp only [GlobalAllocationMachine.initExtra, enabled, rootEq, race, unchanged,
    MemoryExtras.initAllocation, noExtras, MemoryExtras.putAllocation,
    get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, EStateM.tryCatch, tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
    Option.map_none, Option.getD_none, Bool.false_eq_true, ite_false]

theorem root_node (root : BorTag) (size : Size) :
    (BorrowTree.new root size).nodeAt ⟨0⟩ = some {
      tag := root, parent := none, children := #[], defaultInitialPermission := .Disabled,
      defaultInitialSifa := .None, isExposed := false } := by rfl
theorem root_locations (root : BorTag) (size : Size) :
    (BorrowTree.new root size).locations = Miri.DataStructures.DedupRangeMap.new size {
      perms := ({} : UniValMap Tree.LocationState).insert ⟨0⟩ ⟨.Unique,true,.None⟩,
      exposedCache := {} } := by rfl
end DuplicatePrefix.GlobalDataOnlyExtra

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GlobalDataOnlyExtra.init_extra, ``DuplicatePrefix.GlobalDataOnlyExtra.root_node,
      ``DuplicatePrefix.GlobalDataOnlyExtra.root_locations] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved global allocation extra dependency {dependency}"
