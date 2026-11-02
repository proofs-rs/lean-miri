import duplicate_prefix.GlobalAddressManagedBumpState
import duplicate_prefix.GeneralBorrowGcMachineMemoryRetentionRun
namespace DuplicatePrefix.GlobalAddressGcSizeFormation
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GlobalAddressManagedBumpState GlobalAddressLiveSizeFormation
open GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem row_preserves [DecidableEq K] (roots : Roots) (state : MachineHooks.State K User)
    (entries : Array AllocAddresses.InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Rows state.machine.memory entries sizes) (id : AllocId) :
    Rows (stateOf (row roots id state)).machine.memory entries sizes := by
  cases found : state.machine.memory.live.find? (·.1 == id) with
  | none => simpa [row,found,stateOf,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using initial
  | some entry =>
    have idEq : entry.1=id := by have := Array.find?_some found;simpa using this
    obtain ⟨id',allocation⟩ := entry
    simp only at idEq
    subst id'
    have replaced := MemoryCopyBridge.set_live_exact state.machine.memory id allocation
      (allocation.allocation.setExtra (allocation.allocation.extra.removeUnreachableTags roots.tags).tree) found
    have kept : Rows (source_range_insert_live state.machine.memory id
        {allocation with allocation:=allocation.allocation.setExtra (allocation.allocation.extra.removeUnreachableTags roots.tags).tree}) entries sizes := by
      intro query member
      exact replace_extra state.machine.memory id query.allocId allocation _ found _ (initial query member)
    unfold_internal_at ".MemoryState.insertLive" at kept
    cases outcome : (allocation.allocation.extra.removeUnreachableTags roots.tags).outcome <;>
      simpa [row,found,replaced,outcome,Except.mapError,stateOf,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
        pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
        using kept

theorem rows_preserves [DecidableEq K] (roots : Roots) (ids : List (AllocId × LocalAllocation Provenance BorrowTree K))
    (state : MachineHooks.State K User) (entries : Array AllocAddresses.InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Rows state.machine.memory entries sizes) : Rows (stateOf (rows roots ids state)).machine.memory entries sizes := by
  induction ids generalizing state with
  | nil => exact initial
  | cons id rest ih =>
    have first := row_preserves roots state entries sizes initial id.1
    cases done : row roots id.1 state with
    | error error next => simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using first
    | ok control next =>
      cases control with
      | done unit => simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using first
      | yield unit =>
        have tail := ih next (by simpa [done,stateOf] using first)
        simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using tail

theorem finish_preserves (h : Hooks K User) (roots : Roots) (state : MachineHooks.State K User)
    (entries : Array AllocAddresses.InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Rows state.machine.memory entries sizes) :
    Rows (stateOf (GeneralBorrowGcMachineMemoryRetentionRun.finish h roots state)).machine.memory entries sizes := by
  intro query member
  exact gc state.machine.memory query.allocId _ (initial query member) roots.allocations

theorem prune_preserves [DecidableEq K] (h : Hooks K User) (roots : Roots)
    (original state : MachineHooks.State K User) (entries : Array AllocAddresses.InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Rows state.machine.memory entries sizes) :
    Rows (stateOf (GeneralBorrowGcMachineMemoryRetentionRun.prune h roots original state)).machine.memory entries sizes := by
  unfold GeneralBorrowGcMachineMemoryRetentionRun.prune
  split
  · have preserved := rows_preserves roots original.machine.memory.live.toList state entries sizes initial
    cases done : rows roots original.machine.memory.live.toList state with
    | error error next => simpa [bind,EStateM.bind,done,stateOf] using preserved
    | ok unit next =>
      simpa only [bind,EStateM.bind,done] using finish_preserves h roots next entries sizes (by simpa [done,stateOf] using preserved)
  · exact finish_preserves h roots state entries sizes initial

/-- The full actual provenance collector preserves every cached live-data or
MEMORY/STATIC size supplier on both final outcomes. This theorem concerns the
original inverse rows; it does not assume a successful collector or visitor. -/
theorem run_preserves [DecidableEq K] (h : Hooks K User) (state : MachineHooks.State K User)
    (entries : Array AllocAddresses.InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Rows state.machine.memory entries sizes) :
    Rows (stateOf (ProvenanceGC.run h state)).machine.memory entries sizes := by
  rw [GeneralBorrowGcMachineMemoryRetentionRun.source]
  cases collected : GeneralBorrowGcFrameProvenanceCollection.collect state with
  | error error => simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf] using initial
  | ok first =>
    cases visited : h.visitUser state first with
    | error error => simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,visited,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf] using initial
    | ok roots =>
      simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,visited,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
        using prune_preserves h roots state state entries sizes initial
end DuplicatePrefix.GlobalAddressGcSizeFormation
