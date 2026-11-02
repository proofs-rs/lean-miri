import duplicate_prefix.GlobalAddressBaseCacheFormation
namespace DuplicatePrefix.GlobalAddressBaseCacheGc
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcMachineMemoryRetentionLoop GlobalAddressGcFrames GlobalAddressBaseCacheFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem lookup_filter (entries : Array BaseAddressEntry) (roots : Array AllocId)
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (live : memory.isAllocLive id=true) :
    (entries.filter (fun row=>roots.contains row.allocId || memory.isAllocLive row.allocId)).find? (fun row=>row.allocId==id)=
      entries.find? (fun row=>row.allocId==id) := by
  rw [Array.find?_filter]
  congr 1
  funext row
  by_cases same : row.allocId=id
  · simp [same,live]
  · simp [same]

theorem finish (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (roots : Roots) (state : MachineHooks.State K User)
    (cached : Cached (lens.get state.machine.user).addresses)
    (live : ∀row∈(lens.get state.machine.user).addresses.intToPtrMap,state.machine.memory.isAllocLive row.allocId=true) :
    Cached (lens.get (stateOf (GeneralBorrowGcMachineMemoryRetentionRun.finish (MachineGCRoots.hooks views lens) roots state)).machine.user).addresses := by
  simp only [GeneralBorrowGcMachineMemoryRetentionRun.finish,MachineGCRoots.hooks,get,getThe,MonadStateOf.get,EStateM.get,
    bind,EStateM.bind,pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,stateOf,lens.getPut]
  intro row member
  exact (lookup_filter _ roots.allocations state.machine.memory row.allocId (live row member)).trans (cached row member)

theorem prune [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (roots : Roots) (original state : MachineHooks.State K User)
    (cached : Cached (lens.get state.machine.user).addresses)
    (live : ∀row∈(lens.get state.machine.user).addresses.intToPtrMap,state.machine.memory.isAllocLive row.allocId=true) :
    Cached (lens.get (stateOf (GeneralBorrowGcMachineMemoryRetentionRun.prune (MachineGCRoots.hooks views lens) roots original state)).machine.user).addresses := by
  unfold GeneralBorrowGcMachineMemoryRetentionRun.prune
  split
  · have first:=rows_frame roots original.machine.memory.live.toList state
    cases done : rows roots original.machine.memory.live.toList state with
    | error error next =>
      have user : next.machine.user=state.machine.user := by simpa [done,stateOf] using first.1
      simpa only [bind,EStateM.bind,done,stateOf,user] using cached
    | ok unit next =>
      have user : next.machine.user=state.machine.user := by simpa [done,stateOf] using first.1
      have domain : ∀query,next.machine.memory.isAllocLive query=state.machine.memory.isAllocLive query := by simpa [done,stateOf] using first.2
      have nextCached : Cached (lens.get next.machine.user).addresses := by simpa only [user] using cached
      have nextLive : ∀row∈(lens.get next.machine.user).addresses.intToPtrMap,next.machine.memory.isAllocLive row.allocId=true := by
        intro row member
        rw [domain]
        exact live row (by simpa only [user] using member)
      simpa only [bind,EStateM.bind,done,stateOf] using finish views lens roots next nextCached nextLive
  · exact finish views lens roots state cached live

theorem run [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (state : MachineHooks.State K User)
    (cached : Cached (lens.get state.machine.user).addresses)
    (live : ∀row∈(lens.get state.machine.user).addresses.intToPtrMap,state.machine.memory.isAllocLive row.allocId=true) :
    Cached (lens.get (stateOf (MachineGCRoots.run views lens state)).machine.user).addresses := by
  unfold MachineGCRoots.run
  rw [GeneralBorrowGcMachineMemoryRetentionRun.source]
  cases collected : GeneralBorrowGcFrameProvenanceCollection.collect state with
  | error error => simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf] using cached
  | ok first =>
    cases visited : (MachineGCRoots.hooks views lens).visitUser state first with
    | error error => simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,visited,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,stateOf] using cached
    | ok roots =>
      simpa [GeneralBorrowGcMachineMemoryRetentionRun.execute,GeneralBorrowGcMachineMemoryRetentionRun.liftRoots,collected,visited,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
        using prune views lens roots state state cached live
end DuplicatePrefix.GlobalAddressBaseCacheGc
