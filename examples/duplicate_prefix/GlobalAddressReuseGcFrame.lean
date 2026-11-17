import duplicate_prefix.GlobalAddressReuseLifecycleResources
namespace DuplicatePrefix.GlobalAddressReuseGcFrame
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcMachineMemoryRetentionLoop GlobalAddressGcFrames
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem finish_frame (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (roots : Roots) (state : MachineHooks.State K User) :
    let final := stateOf (GeneralBorrowGcMachineMemoryRetentionRun.finish (MachineGCRoots.hooks views lens) roots state)
    (lens.get final.machine.user).addresses.generation = (lens.get state.machine.user).addresses.generation ∧
    (lens.get final.machine.user).addresses.addressMode = (lens.get state.machine.user).addresses.addressMode ∧
    ∀ query, final.machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  simp only [GeneralBorrowGcMachineMemoryRetentionRun.finish,MachineGCRoots.hooks,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,stateOf,lens.getPut]
  exact ⟨True.intro,True.intro,fun _=>rfl⟩

theorem prune_frame [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (roots : Roots) (original state : MachineHooks.State K User) :
    let final := stateOf (GeneralBorrowGcMachineMemoryRetentionRun.prune (MachineGCRoots.hooks views lens) roots original state)
    (lens.get final.machine.user).addresses.generation = (lens.get state.machine.user).addresses.generation ∧
    (lens.get final.machine.user).addresses.addressMode = (lens.get state.machine.user).addresses.addressMode ∧
    ∀ query, final.machine.memory.isAllocLive query = state.machine.memory.isAllocLive query := by
  unfold GeneralBorrowGcMachineMemoryRetentionRun.prune
  split
  · have first := rows_frame roots original.machine.memory.live.toList state
    cases done : rows roots original.machine.memory.live.toList state with
    | error error next =>
      have middle : next.machine.user=state.machine.user ∧ ∀query,next.machine.memory.isAllocLive query=state.machine.memory.isAllocLive query := by simpa [done,stateOf] using first
      have inverse := congrArg (fun user => (lens.get user).addresses.generation) middle.1
      have exposed := congrArg (fun user => (lens.get user).addresses.addressMode) middle.1
      simpa only [bind,EStateM.bind,done,stateOf] using And.intro inverse ⟨exposed,middle.2⟩
    | ok unit next =>
      have middle : next.machine.user=state.machine.user ∧ ∀query,next.machine.memory.isAllocLive query=state.machine.memory.isAllocLive query := by simpa [done,stateOf] using first
      have last := finish_frame views lens roots next
      have kept := And.intro (last.1.trans (congrArg (fun user => (lens.get user).addresses.generation) middle.1))
        (And.intro (last.2.1.trans (congrArg (fun user => (lens.get user).addresses.addressMode) middle.1)) (fun query=>(last.2.2 query).trans (middle.2 query)))
      simpa only [bind,EStateM.bind,done] using kept
  · exact finish_frame views lens roots state

/-- The complete actual machine GC preserves inverse/exposed rows and actual
allocation liveness on BOTH outcomes. AddressLens laws, not an asserted final
frame or successful operation, justify the source metadata writes. -/
theorem run_frame [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (state : MachineHooks.State K User) :
    let final := stateOf (MachineGCRoots.run views lens state)
    (lens.get final.machine.user).addresses.generation = (lens.get state.machine.user).addresses.generation ∧
    (lens.get final.machine.user).addresses.addressMode = (lens.get state.machine.user).addresses.addressMode ∧
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
end DuplicatePrefix.GlobalAddressReuseGcFrame
