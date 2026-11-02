import duplicate_prefix.GeneralBorrowCausalGraphFormation
import duplicate_prefix.GeneralBorrowEffectfulTreeUpdateFrame
import duplicate_prefix.RetagEntry
import Miri.Interpreter.MemoryCopyMachine
namespace DuplicatePrefix.GeneralBorrowActualAccessCausalFrame
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.Interpreter
open GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowCausalGraphFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Canonical PlaceMachine's returned tree keeps generation evidence for every
access status. The separate callback machine state is NOT asserted unchanged. -/
theorem extra_preserves {K U : Type} (config : PlaceMachine.AccessConfig K U) (write : Bool)
    (state : PlaceMachine.AccessState K U) (tree : BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (formed : Formed tree) :
    Formed (PlaceMachine.memoryAccess config write state tree id provenance range).extra := by
  unfold PlaceMachine.memoryAccess
  simp only [Id.run,pure]
  repeat' first
    | exact formed
    | exact Formed.access formed provenance range.start range.size _ _ .VisitChildrenOfAccessed
    | split

open Lean Elab Term Tactic in
private def sourceName : CoreM Name := do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".memoryAccess" && name.toString.contains "Interpreter.MemoryCopyMachine" then some name else none
  match names with
  | [name] => return name
  | _ => throwError "expected exact Interpreter.MemoryCopyMachine.memoryAccess"
open Lean Elab Term in
elab "actual_causal_copy_access" : term => do return mkConst (←sourceName)
open Lean Elab Tactic in
elab "unfold_actual_causal_copy_access" : tactic => do
  let name := mkIdent (←sourceName)
  evalTactic (← `(tactic| unfold $name:ident))

/-- The canonical copy adapter's returned MEMORY preserves all-live formation
on every access outcome. Its generic callback STATE may have other effects;
this theorem refers precisely to the memory field later synchronized by copy.
Only a pre-call allocation lookup is supplied, never access success or NoUB. -/
theorem copy_memory_preserves {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (write : Bool)
    (state : MemoryCopyMachine.GenericState K U) (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (pointer : Pointer (Option Provenance)) (provenance : ProvenanceExtra) (range : AllocRange)
    (before : AllTrees (fun _ tree => Formed tree) memory) :
    AllTrees (fun _ tree => Formed tree)
      (actual_causal_copy_access config write state memory entry.allocation pointer id provenance range).memory := by
  have source := before (id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present))
  have after := extra_preserves config write {state with machine:={state.machine with memory}} entry.allocation.extra id provenance range source
  unfold_actual_causal_copy_access
  simp only [Id.run,pure]
  rw [MemoryCopyBridge.set_live_exact memory id entry _ present]
  exact GeneralBorrowEffectfulTreeUpdateFrame.updated _ memory id entry _ before after
end DuplicatePrefix.GeneralBorrowActualAccessCausalFrame
