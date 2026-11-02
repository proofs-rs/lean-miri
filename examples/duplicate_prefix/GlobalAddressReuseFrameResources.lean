import duplicate_prefix.GlobalAddressReuseGcFrame
namespace DuplicatePrefix.GlobalAddressReuseFrameResources
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressReuseResources GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem expose_frame (addresses : GlobalAddressState) (provenance : Provenance) (live : Option Bool)
    (tracking : Bool) (hook : Option (Except String Unit)) :
    (addresses.exposeProvenance provenance live tracking hook).state.generation=addresses.generation ∧
    (addresses.exposeProvenance provenance live tracking hook).state.addressMode=addresses.addressMode := by
  cases provenance with
  | wildcard => exact ⟨rfl,rfl⟩
  | concrete id tag =>
    unfold GlobalAddressState.exposeProvenance
    dsimp only
    split
    · exact ⟨rfl,rfl⟩
    · cases live with
      | none => exact ⟨rfl,rfl⟩
      | some live =>
        cases live with
        | false => exact ⟨rfl,rfl⟩
        | true =>
          cases tracking with
          | false => exact ⟨rfl,rfl⟩
          | true => cases hook with
            | none => exact ⟨rfl,rfl⟩
            | some value => cases value <;> exact ⟨rfl,rfl⟩

theorem expose {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (generation : AddressGenerationState) (sizes : AllocId → Size) (initial : State memory addresses generation sizes)
    (provenance : Provenance) (tracking : Bool) (hook : Option (Except String Unit)) :
    let live:=match provenance with | .wildcard=>none | .concrete id _=>some (memory.isAllocLive id)
    State memory (addresses.exposeProvenance provenance live tracking hook).state generation sizes := by
  dsimp only
  let live:=match provenance with | .wildcard=>none | .concrete id _=>some (memory.isAllocLive id)
  have frame:=expose_frame addresses provenance live tracking hook
  have inverse:=GlobalAddressExposureFormation.expose_inverse addresses provenance live tracking hook
  refine ⟨GlobalAddressRangeResources.expose memory addresses sizes initial.resources provenance tracking hook,
    frame.1.trans initial.generationEq,frame.2.trans initial.managed,initial.cursor,?_,?_,initial.bounded,initial.pairwise⟩
  · rw [inverse];exact initial.frontier
  · rw [inverse];exact initial.holes

/-- Actual complete machine GC preserves all address/reuse resources on every
outcome, including user root-visitor and tree-collector failures. -/
theorem gc [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (state : MachineHooks.State K User)
    (generation : AddressGenerationState) (sizes : AllocId → Size)
    (initial : State state.machine.memory (lens.get state.machine.user).addresses generation sizes) :
    let final:=stateOf (MachineGCRoots.run views lens state)
    State final.machine.memory (lens.get final.machine.user).addresses generation sizes := by
  dsimp only
  have frame:=GlobalAddressGcFrames.run_frame views lens state
  have generationFrame:=GlobalAddressReuseGcFrame.run_frame views lens state
  refine ⟨GlobalAddressGcRangeResources.run views lens state sizes initial.resources,
    generationFrame.1.trans initial.generationEq,generationFrame.2.1.trans initial.managed,initial.cursor,
    ?_,?_,initial.bounded,initial.pairwise⟩
  · rw [frame.1];exact initial.frontier
  · rw [frame.1];exact initial.holes
end DuplicatePrefix.GlobalAddressReuseFrameResources
