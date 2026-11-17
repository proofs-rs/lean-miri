import duplicate_prefix.GeneralBorrowGcMachineMemoryRetentionLoop
namespace DuplicatePrefix.GeneralBorrowGcMachineMemoryRetentionRun
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcMachineMemoryRetention GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Meta Elab in
elab "gc_source_lift" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".ProvenanceGC.lift" then some name else none
  match names with
  | [name] => mkConstWithFreshMVarLevels name
  | _ => throwError "expected unique source GC lift"

private theorem lift_source (value : Except StepError A) :
    (gc_source_lift value : MachineHooks.M K User A) =
      (match value with | .ok result => pure result | .error error => throw error) := by
  cases value <;> rfl

private def exactRow [DecidableEq K] (roots : Roots) (id : AllocId) : MachineHooks.M K User (ForInStep PUnit) := do
  let machine := (←get).machine
  let some entry := machine.memory.live.find? (·.1 == id) | throw (.invalidProgram "GC live allocation disappeared")
  let result := entry.2.allocation.extra.removeUnreachableTags roots.tags
  let memory ← gc_source_lift ((machine.memory.setLiveAllocation id (entry.2.allocation.setExtra result.tree)).mapError
    (fun error => StepError.invalidProgram s!"GC tree replacement: {reprStr error}"))
  modify fun s => {s with machine:={s.machine with memory}}
  match result.outcome with
  | .ok () => pure ()
  | .error error => throw (.invalidProgram s!"GC tree invariant: {reprStr error}")
  return .yield PUnit.unit

private theorem row_source [DecidableEq K] (roots : Roots) (id : AllocId) :
    (exactRow roots id : MachineHooks.M K User (ForInStep PUnit)) = row roots id := by
  funext state
  unfold exactRow row
  simp only [lift_source,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  cases found : state.machine.memory.live.find? (·.1 == id) with
  | none => rfl
  | some entry =>
    simp only [found]
    cases replaced : (state.machine.memory.setLiveAllocation id
      (entry.2.allocation.setExtra (entry.2.allocation.extra.removeUnreachableTags roots.tags).tree)).mapError
      (fun error => StepError.invalidProgram s!"GC tree replacement: {reprStr error}") <;>
      simp only [replaced,EStateM.bind,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,
        modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    all_goals cases (entry.2.allocation.extra.removeUnreachableTags roots.tags).outcome <;> rfl

def finish (h : Hooks K User) (roots : Roots) : MachineHooks.M K User Unit := do
  let machine := (←get).machine
  let live := fun id => roots.allocations.contains id || machine.memory.isAllocLive id
  let allocationSpans := machine.allocationSpans.filter (fun entry => live entry.1)
  let user := h.setSymbolicAlignment ((h.symbolicAlignment machine.user).filter (fun entry => live entry.1)) machine.user
  let addresses := h.addresses user
  let user := h.setAddresses {addresses with baseAddr:=addresses.baseAddr.filter (fun entry => live entry.allocId)} user
  let borrowTracker := machine.borrowTracker.map fun borrow => {borrow with global:=
    {borrow.global with rootPointerTags:=borrow.global.rootPointerTags.filter (fun entry => live entry.1)}}
  let memory := machine.memory.removeUnreachable roots.allocations
  modify fun s => {s with machine:={s.machine with allocationSpans,user,borrowTracker,memory}}

def prune [DecidableEq K] (h : Hooks K User) (roots : Roots) (original : MachineHooks.State K User) : MachineHooks.M K User Unit := do
  if original.machine.borrowTracker.isSome then
    let _ ← rows roots original.machine.memory.live.toList
  finish h roots

def liftRoots (value : Except StepError Roots) : MachineHooks.M K User Roots :=
  match value with | .ok roots => pure roots | .error error => throw error

def execute [DecidableEq K] (h : Hooks K User) : MachineHooks.M K User Unit := do
  let state ← get
  let collected ← liftRoots (GeneralBorrowGcFrameProvenanceCollection.collect state)
  let roots ← liftRoots (h.visitUser state collected)
  prune h roots state

private theorem allocation_scan (items : List (AllocId × LocalAllocation Provenance BorrowTree K))
    (enabled : Bool) (roots : Roots) (state : MachineHooks.State K User) :
    (forIn (m:=MachineHooks.M K User) items roots (fun entry acc =>
      pure (.yield (acc.allocation enabled entry.2.allocation)))) state =
    .ok (Id.run (forIn (m:=Id) items roots (fun entry acc =>
      pure (.yield (acc.allocation enabled entry.2.allocation))))) state := by
  induction items generalizing roots with
  | nil => rfl
  | cons first rest ih =>
    simpa only [List.forIn_cons,bind,EStateM.bind,pure,EStateM.pure,Id.run,Id.instMonad] using
      ih (roots.allocation enabled first.2.allocation)

private theorem allocation_scan_action (items : List (AllocId × LocalAllocation Provenance BorrowTree K))
    (enabled : Bool) (roots : Roots) :
    (forIn (m:=MachineHooks.M K User) items roots (fun entry acc =>
      pure (.yield (acc.allocation enabled entry.2.allocation)))) =
    pure (Id.run (forIn (m:=Id) items roots (fun entry acc =>
      pure (.yield (acc.allocation enabled entry.2.allocation))))) := by
  funext state
  exact allocation_scan items enabled roots state

/-- The factored traversal is the production machine collector, including all
error paths and the post-traversal dead-memory and metadata pruning. -/
theorem source [DecidableEq K] (h : Hooks K User) : ProvenanceGC.run h = execute h := by
  funext state
  unfold ProvenanceGC.run execute GeneralBorrowGcFrameProvenanceCollection.collect
  unfold prune finish rows liftRoots
  simp only [←row_source]
  unfold exactRow
  unfold GeneralBorrowGcFrameProvenanceCollection.allocationRoots
  simp only [lift_source,←Array.forIn_toList,allocation_scan_action]
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  let seed : Roots := Id.run (forIn (m:=Id) state.machine.memory.live.toList {} (fun entry acc =>
    pure (.yield (acc.allocation state.machine.borrowTracker.isSome entry.2.allocation))))
  cases collected : seed.stack state.stack <;>
    simp only [seed] at collected
  all_goals simp only [collected,EStateM.bind,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  all_goals try rfl
  all_goals rename_i first
  all_goals cases visited : h.visitUser state first
  all_goals simp only [visited,EStateM.bind,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  all_goals try rfl
  all_goals cases enabled : state.machine.borrowTracker.isSome <;>
    simp only [enabled,Bool.false_eq_true,Bool.true_eq,↓reduceIte]
  all_goals rfl

theorem finish_preserves (h : Hooks K User) (roots : Roots) (state : MachineHooks.State K User)
    (id : AllocId) (index : UniIndex) (tag : BorTag) (stored : Stored state.machine.memory id index tag) :
    Stored (stateOf (finish h roots state)).machine.memory id index tag := stored

theorem prune_preserves [DecidableEq K] (h : Hooks K User) (roots : Roots)
    (original state : MachineHooks.State K User) (id : AllocId) (index : UniIndex) (tag : BorTag)
    (stored : Stored state.machine.memory id index tag) (held : roots.tags.contains tag=true) :
    Stored (stateOf (prune h roots original state)).machine.memory id index tag := by
  unfold prune
  split
  · have preserved := rows_preserves roots original.machine.memory.live.toList state id index tag stored held
    cases done : rows roots original.machine.memory.live.toList state with
    | error error next => simpa [bind,EStateM.bind,done,stateOf] using preserved
    | ok unit next =>
      simpa only [bind,EStateM.bind,done] using finish_preserves h roots next id index tag (by simpa [done,stateOf] using preserved)
  · exact finish_preserves h roots state id index tag stored

/-- A conditional visitor-root property is enough: the visitor may fail. The
collector's actual final memory, on success OR failure, retains the source node
and coherent mapping. No callback success or collector success is assumed. -/
theorem run_preserves [DecidableEq K] (h : Hooks K User) (state : MachineHooks.State K User)
    (id : AllocId) (index : UniIndex) (tag : BorTag) (stored : Stored state.machine.memory id index tag)
    (rootsHeld : ∀ collected roots, GeneralBorrowGcFrameProvenanceCollection.collect state = .ok collected →
      h.visitUser state collected = .ok roots → roots.tags.contains tag=true) :
    Stored (stateOf (ProvenanceGC.run h state)).machine.memory id index tag := by
  rw[source]
  cases collected : GeneralBorrowGcFrameProvenanceCollection.collect state with
  | error error => simpa [execute,liftRoots,collected,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
      throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf] using stored
  | ok first =>
    cases visited : h.visitUser state first with
    | error error => simpa [execute,liftRoots,collected,visited,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
        pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf] using stored
    | ok roots =>
      simpa [execute,liftRoots,collected,visited,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
        using prune_preserves h roots state state id index tag stored (rootsHeld first roots collected visited)
end DuplicatePrefix.GeneralBorrowGcMachineMemoryRetentionRun
