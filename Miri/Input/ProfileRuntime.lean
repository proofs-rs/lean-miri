import Miri.Input.RuntimeCtfeQueryMachine
import Miri.Input.CompilerInitialCtfeQueryStore
import Miri.Input.ProfilePreparation
import Miri.Input.CompilerInitialAllocationBytes
import Miri.Input.CompilerInitialAllocationByteMachine

/-! Profile-preserving machine adapters. The typed store never owns a second
memory snapshot: operations pair it with the current machine MemoryState. -/
namespace Miri.Input.ProfileRuntime
open Lean Miri.Memory Miri.Interpreter
set_option autoImplicit false
variable {K User : Type}

def arrays (prepared : ProfilePreparation.Prepared) : RuntimeArrayTypes.World :=
  prepared.base.types

def bytes (prepared : ProfilePreparation.Prepared)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) :
    Except String CompilerGlobalBytes.Prepared := do
  match prepared with
  | .legacy common =>
    (CompilerGlobalBytes.prepare common.compiler.program common.compiler.runtime memory).mapError toString
  | .initial initial _ _ =>
    let some run := memory.activeInitialCompilerRun
      | throw "complete initial profile has no active shared source counter"
    CompilerInitialAllocation.Bytes.prepare initial.compiler.program initial.compiler.runtime run
      {initial.initialWorld with memory}

/-- Called exactly once after machine construction and before source startup.
The lawful concrete User adapter makes this state visible to every byte reserve. -/
def installStoreState (access : CompilerInitialAllocation.ByteMachine.Access User)
    (prepared : ProfilePreparation.Prepared) (state : MachineHooks.State K User) :
    Except StepError (MachineHooks.State K User) := do
  match prepared with
  | .legacy _ =>
    if (access.getStore state.machine.user).isSome || state.machine.memory.activeInitialCompilerRun.isSome then
      throw (.invalidProgram "legacy profile cannot own an initial compiler store/counter")
    pure state
  | .initial initial _ _ =>
    if (access.getStore state.machine.user).isSome then
      throw (.invalidProgram "initial compiler store already installed")
    let some run := state.machine.memory.activeInitialCompilerRun
      | throw (.invalidProgram "initial compiler shared source counter absent")
    unless initial.initialWorld.runs.any (fun row => row.1 == run) do
      throw (.invalidProgram "initial compiler store/counter run mismatch")
    let user := access.setStore initial.initialWorld.store state.machine.user
    pure {state with machine := {state.machine with user}}

def installStore (access : CompilerInitialAllocation.ByteMachine.Access User)
    (prepared : ProfilePreparation.Prepared) : MachineHooks.M K User Unit := do
  let state ← get
  match installStoreState access prepared state with
  | .error error => throw error
  | .ok installed => set installed

/-- Query memo installation happens only at source startup, from the validated
initial capability. All later callbacks use Memo.attach, never this initializer. -/
def installQueriesState (memoAccess : RuntimeCtfeQueryMachine.MemoAccess User)
    (prepared : ProfilePreparation.Prepared) (state : MachineHooks.State K User) :
    Except StepError (MachineHooks.State K User) := do
  match prepared with
  | .legacy _ =>
    if (memoAccess.getMemo state.machine.user).isSome then
      throw (.invalidProgram "legacy profile cannot own the new typed query memo")
    pure state
  | .initial material roots selected =>
    if (memoAccess.getMemo state.machine.user).isSome then
      throw (.invalidProgram "initial compiler query memo already installed")
    let [(run,_)] := material.initialWorld.runs.toList
      | throw (.invalidProgram "initial query memo requires one compiler run")
    let query ← match CompilerInitialCtfeQueryStore.init material.compiler material.image material.types roots run material.initialWorld with
      | .ok query => pure query
      | .error error => throw (.unsupported error)
    let memo ← match RuntimeCtfeQueryMachine.Memo.create query.memo selected with
      | .ok memo => pure memo
      | .error error => throw (.unsupported error)
    pure {state with machine := {state.machine with user := memoAccess.setMemo memo state.machine.user}}

end Miri.Input.ProfileRuntime
