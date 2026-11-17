import duplicate_prefix.GlobalAddressGcFrames
namespace DuplicatePrefix.GlobalAddressGcRangeResources
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowGcMachineMemoryRetentionLoop GlobalAddressRangeResources
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual full GC preserves the recurring raw address-range/size certificate,
including early root-visitor errors and later committed tree-collector errors.
The real lawful AddressLens supplies the final inverse/exposed frame; no final
geometry, metadata or operation-success premise is supplied. -/
theorem run [DecidableEq K] (views : MachineGCRoots.Views User Os R Payload H D O)
    (lens : FunctionPointers.AddressLens User AddressPayload) (state : MachineHooks.State K User) (sizes : AllocId → Size)
    (initial : State state.machine.memory (lens.get state.machine.user).addresses sizes) :
    let final := stateOf (MachineGCRoots.run views lens state)
    State final.machine.memory (lens.get final.machine.user).addresses sizes := by
  dsimp only
  have frame := GlobalAddressGcFrames.run_frame views lens state
  have metadata := GlobalAddressGcSizeFormation.run_preserves (MachineGCRoots.hooks views lens) state
    (lens.get state.machine.user).addresses.intToPtrMap sizes initial.rows
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · constructor
    · intro row member
      rw [frame.1] at member
      rw [frame.2.2]
      exact initial.recurring.live.1 row member
    · intro id member
      rw [frame.2.1] at member
      rw [frame.2.2]
      exact initial.recurring.live.2 id member
  · rw [frame.1]
    exact initial.recurring.ordered
  · rw [frame.1]
    exact initial.recurring.unique
  · rw [frame.1]
    exact initial.apart
  · rw [frame.1]
    exact metadata
end DuplicatePrefix.GlobalAddressGcRangeResources
