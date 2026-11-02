import duplicate_prefix.GlobalEmptyRootArgumentScope

namespace DuplicatePrefix.GlobalEmptyRootPrepared
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem lookup_other {A : Type} (rows : Array (AllocId × A)) (id other : AllocId) (value : A)
    (different : other ≠ id) :
    ((rows.filter (fun row => row.1 != id)).push (id,value)).find? (fun row => row.1 == other) =
      rows.find? (fun row => row.1 == other) := by
  have filtered : (rows.filter (fun row => row.1 != id)).find? (fun row => row.1 == other) =
      rows.find? (fun row => row.1 == other) := by
    rw [Array.find?_filter]
    congr 1
    funext row
    by_cases eqOther : (row.1 == other) = true
    · have equality : row.1 = other := beq_iff_eq.mp eqOther
      have neId : row.1 ≠ id := fun h => different (equality.symm.trans h)
      have keep : (row.1 != id) = true := by simpa using neId
      simp [eqOther,keep]
    · simp [eqOther]
  simp [Array.find?_push,Ne.symm different,filtered]

theorem live_other (options : EvalConfigurationCore.Options)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id other : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (different : other ≠ id) :
    (GlobalEmptyRootCopy.preparedMachine options machine id root source converted).memory.live.find?
      (fun row => row.1 == other) = machine.memory.live.find? (fun row => row.1 == other) :=
  lookup_other machine.memory.live id other _ different

theorem extras_other (options : EvalConfigurationCore.Options)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id other : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (different : other ≠ id) :
    (GlobalEmptyRootCopy.preparedMachine options machine id root source converted).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == other) = machine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == other) :=
  lookup_other machine.user.payload.payload.user.runtime.extras.allocations id other _ different
end DuplicatePrefix.GlobalEmptyRootPrepared

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GlobalEmptyRootPrepared.lookup_other,
      ``DuplicatePrefix.GlobalEmptyRootPrepared.live_other,``DuplicatePrefix.GlobalEmptyRootPrepared.extras_other] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved global empty prepared data dependency {dependency}"
