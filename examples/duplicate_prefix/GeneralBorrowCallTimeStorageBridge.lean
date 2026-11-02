import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.GeneralBorrowRawSliceBytes
namespace DuplicatePrefix.GeneralBorrowCallTimeStorageBridge
open Miri Miri.Input Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The existing S01 reference-storage candidate supplies the SAME initial
allocation byte packet used by the checked all-count entry. Only the existing
numeric backend margin is separate; no operation result is an assumption. -/
theorem bytes {K U : Type}
    {before : MachineHooks.MachineState K (ValidityMachine.UserState U)}
    {pointer : Pointer Provenance} {len : UInt64}
    (input : DuplicatePrefixReferenceInput.Positive before pointer len)
    (room : ∀ row ∈ before.memory.live.toList, row.2.allocation.len+64 < 2^64) :
    GeneralBorrowRawSliceBytes.Data input.entry.allocation input.offset len := by
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  exact {
    slice := by simpa only [input.size,Size.ofBytes] using input.storage
    storage := by simpa only [input.size,Size.ofBytes] using input.bytes
    provenance := input.provenanceMap
    mutable := input.mutable
    storageFits := room (input.id,input.entry) member }

/-- Runtime and resource candidates supply the actual selected allocation's
RuntimeFacts. The tracker identity is derived from the common initial machine;
no chronology/order, successful access or target safety is added. -/
theorem runtime {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {pointer : Pointer Provenance} {len : UInt64}
    (input : DuplicatePrefixReferenceInput.Positive before pointer len)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len) :
    DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global := by
  have same : tracker=input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  exact {
    formed := state.formed (input.id,input.entry) member
    coherent := state.coherent (input.id,input.entry) member
    possible := state.possible (input.id,input.entry) member
    below := resources.tagsBelow (input.id,input.entry) member }

/-- The entry's +5 node/tag margins are consequences of the existing candidate
budget (+16), not additional positive-reference conditions. -/
theorem margins {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState}
    {pointer : Pointer Provenance} {len : UInt64}
    (input : DuplicatePrefixReferenceInput.Positive before pointer len)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : Resources options limits remaining before tracker len) :
    input.entry.allocation.extra.nodes.size+5 < 65536 ∧
    input.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615 := by
  have same : tracker=input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have node := resources.nodeRoom (input.id,input.entry) member
  dsimp only at node
  have tag := resources.tagRoom
  constructor <;> omega

/-- From the existing nonempty branch of the provisional call specification,
extract its actual stored input and discharge bytes/runtime/headroom together.
This is a real implication from that specification; it does NOT prove the
specification covers all valid Rust inputs or the whole Target. -/
theorem positive_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (contract : LegacyContract options limits remaining span before argument len place)
    (nonempty : len ≠ 0) :
    ∃ pointer, ∃ input : DuplicatePrefixReferenceInput.Positive before pointer len,
      argument = .pointer pointer ∧
      GeneralBorrowRawSliceBytes.Data input.entry.allocation input.offset len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global ∧
      input.entry.allocation.extra.nodes.size+5 < 65536 ∧
      input.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615 := by
  cases contract.reference with
  | empty zero metadata => exact False.elim (nonempty zero)
  | positive pointer encoding input =>
    obtain ⟨nodes,tags⟩ := margins input contract.runtime contract.resources
    exact ⟨pointer,input,encoding,bytes input contract.resources.storageRoom,
      runtime input contract.runtime contract.resources,nodes,tags⟩
end DuplicatePrefix.GeneralBorrowCallTimeStorageBridge
