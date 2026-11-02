import duplicate_prefix.GlobalAddressRangeResources
namespace DuplicatePrefix.GlobalAddressGcFrames
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcMachineMemoryRetentionLoop GlobalAddressLiveSizeFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem inserted_domain {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (present : memory.live.find? (·.1 == id) = some (id,entry)) (query : AllocId) :
    (source_range_insert_live memory id {entry with allocation:=entry.allocation.setExtra tree}).isAllocLive query = memory.isAllocLive query := by
  by_cases same : query=id
  · subst query
    have before := MemoryCopyBridge.live_any_of_present memory id entry present
    have after := MemoryCopyBridge.live_any_replaced memory id {entry with allocation:=entry.allocation.setExtra tree}
    unfold_internal ".MemoryState.insertLive"
    simp only [MemoryState.isAllocLive,before,after,Bool.true_or]
  · have predicates : (fun row : AllocId × LocalAllocation Provenance BorrowTree K => (row.1 != id) && (row.1 == query)) = (fun row => row.1 == query) := by
      funext row
      by_cases equal : row.1=query
      · simp [equal,same]
      · simp [equal]
    unfold_internal ".MemoryState.insertLive"
    simp only [MemoryState.isAllocLive,Array.any_push,Array.any_filter,predicates,
      show (id == query) = false from by simpa using Ne.symm same,Bool.or_false]

theorem row_frame [DecidableEq K] (roots : Roots) (state : MachineHooks.State K User) (id : AllocId) :
    (stateOf (row roots id state)).machine.user = state.machine.user ∧
    ∀ query, (stateOf (row roots id state)).machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  cases found : state.machine.memory.live.find? (·.1 == id) with
  | none => simp [row,found,stateOf,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  | some entry =>
    have idEq : entry.1=id := by have := Array.find?_some found;simpa using this
    obtain ⟨id',allocation⟩ := entry
    simp only at idEq
    subst id'
    have replaced := MemoryCopyBridge.set_live_exact state.machine.memory id allocation
      (allocation.allocation.setExtra (allocation.allocation.extra.removeUnreachableTags roots.tags).tree) found
    have domain := inserted_domain state.machine.memory id allocation (allocation.allocation.extra.removeUnreachableTags roots.tags).tree found
    unfold_internal_at ".MemoryState.insertLive" at domain
    cases outcome : (allocation.allocation.extra.removeUnreachableTags roots.tags).outcome <;>
      simpa [row,found,replaced,outcome,Except.mapError,stateOf,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
        pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
        using (show state.machine.user=state.machine.user ∧ _ from ⟨rfl,domain⟩)

theorem rows_frame [DecidableEq K] (roots : Roots) (ids : List (AllocId × LocalAllocation Provenance BorrowTree K))
    (state : MachineHooks.State K User) :
    (stateOf (rows roots ids state)).machine.user = state.machine.user ∧
    ∀ query, (stateOf (rows roots ids state)).machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  induction ids generalizing state with
  | nil => exact ⟨rfl,fun _=>rfl⟩
  | cons id rest ih =>
    have first := row_frame roots state id.1
    cases done : row roots id.1 state with
    | error error next => simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using first
    | ok control next =>
      cases control with
      | done unit => simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using first
      | yield unit =>
        have middle : next.machine.user=state.machine.user ∧ ∀query,next.machine.memory.isAllocLive query=state.machine.memory.isAllocLive query := by simpa [done,stateOf] using first
        have tail := ih next
        have kept := And.intro (tail.1.trans middle.1) (fun query => (tail.2 query).trans (middle.2 query))
        simpa [rows,List.forIn_cons,bind,EStateM.bind,done,stateOf,pure,EStateM.pure] using kept

/-- Lawful actual AddressLens writes prune base-address/symbolic metadata,
while preserving both source inverse-vector and exposure membership. -/
theorem finish_frame (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (roots : Roots) (state : MachineHooks.State K User) :
    let final := stateOf (GeneralBorrowGcMachineMemoryRetentionRun.finish (MachineGCRoots.hooks views lens) roots state)
    (lens.get final.machine.user).addresses.intToPtrMap = (lens.get state.machine.user).addresses.intToPtrMap ∧
    (lens.get final.machine.user).addresses.exposed = (lens.get state.machine.user).addresses.exposed ∧
    ∀ query, final.machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  simp only [GeneralBorrowGcMachineMemoryRetentionRun.finish,MachineGCRoots.hooks,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,stateOf,lens.getPut]
  exact ⟨True.intro,True.intro,fun _=>rfl⟩

theorem prune_frame [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (roots : Roots) (original state : MachineHooks.State K User) :
    let final := stateOf (GeneralBorrowGcMachineMemoryRetentionRun.prune (MachineGCRoots.hooks views lens) roots original state)
    (lens.get final.machine.user).addresses.intToPtrMap = (lens.get state.machine.user).addresses.intToPtrMap ∧
    (lens.get final.machine.user).addresses.exposed = (lens.get state.machine.user).addresses.exposed ∧
    ∀ query, final.machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  unfold GeneralBorrowGcMachineMemoryRetentionRun.prune
  split
  · have first := rows_frame roots original.machine.memory.live.toList state
    cases done : rows roots original.machine.memory.live.toList state with
    | error error next =>
      have middle : next.machine.user=state.machine.user ∧ ∀query,next.machine.memory.isAllocLive query=state.machine.memory.isAllocLive query := by simpa [done,stateOf] using first
      have inverse := congrArg (fun user => (lens.get user).addresses.intToPtrMap) middle.1
      have exposed := congrArg (fun user => (lens.get user).addresses.exposed) middle.1
      simpa only [bind,EStateM.bind,done,stateOf] using And.intro inverse ⟨exposed,middle.2⟩
    | ok unit next =>
      have middle : next.machine.user=state.machine.user ∧ ∀query,next.machine.memory.isAllocLive query=state.machine.memory.isAllocLive query := by simpa [done,stateOf] using first
      have last := finish_frame views lens roots next
      have kept := And.intro (last.1.trans (congrArg (fun user => (lens.get user).addresses.intToPtrMap) middle.1))
        (And.intro (last.2.1.trans (congrArg (fun user => (lens.get user).addresses.exposed) middle.1)) (fun query=>(last.2.2 query).trans (middle.2 query)))
      simpa only [bind,EStateM.bind,done] using kept
  · exact finish_frame views lens roots state

/-- The complete actual machine GC preserves inverse/exposed rows and actual
allocation liveness on BOTH outcomes. AddressLens laws, not an asserted final
frame or successful operation, justify the source metadata writes. -/
theorem run_frame [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (state : MachineHooks.State K User) :
    let final := stateOf (MachineGCRoots.run views lens state)
    (lens.get final.machine.user).addresses.intToPtrMap = (lens.get state.machine.user).addresses.intToPtrMap ∧
    (lens.get final.machine.user).addresses.exposed = (lens.get state.machine.user).addresses.exposed ∧
    ∀ query, final.machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  unfold MachineGCRoots.run
  rw [GeneralBorrowGcMachineMemoryRetentionRun.source]
  cases collected : GeneralBorrowGcFrameProvenanceCollection.collect state with
  | error error => simp [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf]
  | ok first =>
    cases visited : (MachineGCRoots.hooks views lens).visitUser state first with
    | error error => simp [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,visited,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf]
    | ok roots =>
      simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,visited,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
        using prune_frame views lens roots state state
end DuplicatePrefix.GlobalAddressGcFrames
