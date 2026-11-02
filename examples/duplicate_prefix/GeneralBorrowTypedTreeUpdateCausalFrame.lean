import duplicate_prefix.TypedRetagEntry
import duplicate_prefix.GeneralBorrowEffectfulTreeUpdateFrame
namespace DuplicatePrefix.GeneralBorrowTypedTreeUpdateCausalFrame
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.Interpreter
open TypedRetagEntry GeneralBorrowEffectfulTreeUpdateFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- State retained by the canonical TypedRetag update, including errors. -/
def Holds {K U A : Type} (P : AllocId → BorrowTree → Prop)
    (result : EStateM.Result StepError (MachineHooks.State K U) A) : Prop :=
  match result with
  | .ok _ state => AllTrees P state.machine.memory
  | .error _ state => AllTrees P state.machine.memory

/-- The ACTUAL canonical TypedRetag.updateTree stores only one allocation
extra. It preserves arbitrary all-live tree data invariants on every outcome,
without a successful-update or successful-retag hypothesis. -/
theorem update_preserves {K U : Type} [DecidableEq K]
    (state : MachineHooks.State K U) (P : AllocId → BorrowTree → Prop) (id : AllocId) (tree : BorrowTree)
    (before : AllTrees P state.machine.memory) (replacement : P id tree) :
    Holds P (typed_update_tree id tree state) := by
  cases found : state.machine.memory.live.find? (fun row => row.1 == id) with
  | none =>
    unfold_typed ".TypedRetag.updateTree"
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,found]
    exact before
  | some row =>
    have key : row.1 = id := by simpa only [beq_iff_eq] using Array.find?_some found
    rcases row with ⟨keyId,entry⟩
    dsimp only at key
    subst keyId
    rw [update_tree_present state id entry tree found]
    exact updated P state.machine.memory id entry tree before replacement
end DuplicatePrefix.GeneralBorrowTypedTreeUpdateCausalFrame
