import duplicate_prefix.GeneralBorrowGcMachineMemoryRetention
namespace DuplicatePrefix.GeneralBorrowGcMachineMemoryRetentionLoop
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcMachineMemoryRetention
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Exact production per-allocation body, including committing the mutated tree
before returning an invariant error. -/
def row [DecidableEq K] (roots : Roots) (id : AllocId) : MachineHooks.M K User (ForInStep PUnit) := do
  let machine := (←get).machine
  let some entry := machine.memory.live.find? (·.1 == id) | throw (.invalidProgram "GC live allocation disappeared")
  let result := entry.2.allocation.extra.removeUnreachableTags roots.tags
  let memory ← match (machine.memory.setLiveAllocation id (entry.2.allocation.setExtra result.tree)).mapError
        (fun error => StepError.invalidProgram s!"GC tree replacement: {reprStr error}") with
    | .ok memory => pure memory
    | .error error => throw error
  modify fun s => {s with machine:={s.machine with memory}}
  match result.outcome with
  | .ok () => pure ()
  | .error error => throw (.invalidProgram s!"GC tree invariant: {reprStr error}")
  return .yield PUnit.unit

def rows [DecidableEq K] (roots : Roots) (ids : List (AllocId × LocalAllocation Provenance BorrowTree K)) : MachineHooks.M K User PUnit :=
  forIn ids PUnit.unit (fun entry _ => row roots entry.1)

def stateOf (result : EStateM.Result StepError (MachineHooks.State K User) A) : MachineHooks.State K User :=
  match result with | .ok _ state => state | .error _ state => state

/-- Every outcome of a real row, including a missing allocation or an invariant
failure after a committed tree replacement, preserves the target node. -/
theorem row_preserves [DecidableEq K] (roots : Roots) (state : MachineHooks.State K User)
    (target : AllocId) (index : UniIndex) (tag : BorTag)
    (stored : Stored state.machine.memory target index tag) (held : roots.tags.contains tag=true) (id : AllocId) :
    Stored (stateOf (row roots id state)).machine.memory target index tag := by
  cases found : state.machine.memory.live.find? (·.1 == id) with
  | none => simpa [row,found,stateOf,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using stored
  | some entry =>
    have idEq : entry.1=id := by
      have := Array.find?_some found
      simpa using this
    obtain ⟨id',allocation⟩ := entry
    simp only at idEq
    subst id'
    have replaced := MemoryCopyBridge.set_live_exact state.machine.memory id allocation
      (allocation.allocation.setExtra (allocation.allocation.extra.removeUnreachableTags roots.tags).tree) found
    have retained := committed state.machine.memory roots target index tag stored held id allocation found
    cases outcome : (allocation.allocation.extra.removeUnreachableTags roots.tags).outcome <;>
      simpa [row,found,replaced,outcome,Except.mapError,stateOf,commit,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
        pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using retained

/-- Arbitrary traversal length and either final outcome, not a successful-run
premise. The source iteration can encounter the target repeatedly. -/
theorem rows_preserves [DecidableEq K] (roots : Roots) (ids : List (AllocId × LocalAllocation Provenance BorrowTree K))
    (state : MachineHooks.State K User) (target : AllocId) (index : UniIndex) (tag : BorTag)
    (stored : Stored state.machine.memory target index tag) (held : roots.tags.contains tag=true) :
    Stored (stateOf (rows roots ids state)).machine.memory target index tag := by
  induction ids generalizing state with
  | nil => exact stored
  | cons id rest ih =>
    have first := row_preserves roots state target index tag stored held id.1
    cases done : row roots id.1 state with
    | error error next => simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using first
    | ok control next =>
      cases control with
      | done unit => simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using first
      | yield unit =>
        have tail := ih next (by simpa [done,stateOf] using first)
        simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using tail
end DuplicatePrefix.GeneralBorrowGcMachineMemoryRetentionLoop
