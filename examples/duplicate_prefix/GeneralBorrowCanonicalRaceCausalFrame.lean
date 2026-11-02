import duplicate_prefix.GeneralBorrowCanonicalRetagQueryFrame
import duplicate_prefix.GeneralBorrowTypedTreeUpdateCausalFrame
namespace DuplicatePrefix.GeneralBorrowCanonicalRaceCausalFrame
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.Interpreter
open GeneralBorrowCanonicalRetagQueryFrame GeneralBorrowEffectfulTreeUpdateFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- The real race detector changes clocks and race metadata, including on an
error. It never changes allocation memory; disabling races is unnecessary. -/
theorem access_memory {K U : Type} (machine : MachineHooks.MachineState K U) (id : AllocId)
    (range : AllocRange) (write : Option Miri.Concurrency.NaWriteType)
    (read : Miri.Concurrency.NaReadType) :
    (MachineHooks.memoryRaceAccess machine id range write read).1.memory = machine.memory := by
  unfold MachineHooks.memoryRaceAccess
  simp only [Id.run,bind,pure]
  repeat' first | rfl | split

theorem read_memory {K U : Type} (state : MachineHooks.State K U) (id : AllocId)
    (range : AllocRange) (kind : Miri.Concurrency.NaReadType) :
    (retained (MachineHooks.memoryRaceRead id range kind state)).machine.memory = state.machine.memory := by
  have frame := access_memory state.machine id range none kind
  unfold MachineHooks.memoryRaceRead
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,set,EStateM.set]
  generalize result : MachineHooks.memoryRaceAccess state.machine id range none kind = pair
  rw [result] at frame
  rcases pair with ⟨machine,outcome⟩
  cases outcome <;> exact frame

theorem write_memory {K U : Type} (state : MachineHooks.State K U) (id : AllocId)
    (range : AllocRange) (kind : Miri.Concurrency.NaWriteType) :
    (retained (MachineHooks.memoryRaceWrite id range kind state)).machine.memory = state.machine.memory := by
  have frame := access_memory state.machine id range (some kind) .Read
  unfold MachineHooks.memoryRaceWrite
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,set,EStateM.set]
  generalize result : MachineHooks.memoryRaceAccess state.machine id range (some kind) .Read = pair
  rw [result] at frame
  rcases pair with ⟨machine,outcome⟩
  cases outcome <;> exact frame

theorem read_preserves {K U : Type} (P : AllocId → BorrowTree → Prop)
    (state : MachineHooks.State K U) (id : AllocId) (range : AllocRange)
    (kind : Miri.Concurrency.NaReadType) (before : AllTrees P state.machine.memory) :
    GeneralBorrowTypedTreeUpdateCausalFrame.Holds P (MachineHooks.memoryRaceRead id range kind state) := by
  have after : AllTrees P (retained (MachineHooks.memoryRaceRead id range kind state)).machine.memory := by
    rw [read_memory];exact before
  cases outcome : MachineHooks.memoryRaceRead id range kind state <;> simpa only [outcome,retained,GeneralBorrowTypedTreeUpdateCausalFrame.Holds] using after

theorem write_preserves {K U : Type} (P : AllocId → BorrowTree → Prop)
    (state : MachineHooks.State K U) (id : AllocId) (range : AllocRange)
    (kind : Miri.Concurrency.NaWriteType) (before : AllTrees P state.machine.memory) :
    GeneralBorrowTypedTreeUpdateCausalFrame.Holds P (MachineHooks.memoryRaceWrite id range kind state) := by
  have after : AllTrees P (retained (MachineHooks.memoryRaceWrite id range kind state)).machine.memory := by
    rw [write_memory];exact before
  cases outcome : MachineHooks.memoryRaceWrite id range kind state <;> simpa only [outcome,retained,GeneralBorrowTypedTreeUpdateCausalFrame.Holds] using after

theorem get_tree_readonly {K U : Type} (id : AllocId) :
    ReadOnly (typed_get_tree id : MachineHooks.M K U BorrowTree) := by
  intro state
  unfold_typed ".TypedRetag.getTree"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
  cases state.machine.memory.live.find? (fun row => row.1 == id) <;> rfl

theorem tracker_readonly {K U : Type} :
    ReadOnly ((typed_tracker) (K := K) (User := U) : MachineHooks.M K U MachineHooks.BorrowState) := by
  intro state
  unfold_typed ".TypedRetag.tracker"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
  cases state.machine.borrowTracker <;> rfl
end DuplicatePrefix.GeneralBorrowCanonicalRaceCausalFrame
