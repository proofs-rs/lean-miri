import duplicate_prefix.CurrentCallEmptyQueryMetadata
import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.GlobalAddressBaseCacheFormation

/-! Query-local selected-target data for the actual empty wildcard frontend.
The supported external-image profile inside TargetMetadata is sufficient data,
not an ordinary-input necessity claim. General image grammar, TLS/extern targets
and uncached materialization remain OPEN. No source loan or byte ownership is
required here. -/
namespace DuplicatePrefix.CurrentCallEmptySelectedHit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixEmptyReferenceInput DuplicatePrefixCallSpecification
open S03WildcardEmptyClassification (Hit)
open WildcardInteriorHitAddress (Cut)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Raw relevant address rows: exact equality or the in-range immediate
predecessor. Exposure is checked separately. No resolver result is an input. -/
def SelectedRow {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) (row : InverseAddressEntry) : Prop :=
  row.address = address ∨ ∃ cut info, Cut addresses.intToPtrMap address cut ∧ cut ≠ 0 ∧
    addresses.intToPtrMap[cut-1]? = some row ∧ memory.getAllocInfo row.allocId = .ok info ∧
    address-row.address < info.size.bytes

/-- Physical map coherence and first-match metadata sources for this query.
Only a selected exposed row needs retag/materialization target data. -/
structure Query {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) : Prop where
  nonstrict : addresses.provenanceMode ≠ .strict
  coherent : GlobalAddressRecurringFormation.State memory addresses
  cached : GlobalAddressBaseCacheFormation.Cached addresses
  predecessor : ∀ cut, Cut addresses.intToPtrMap address cut → cut ≠ 0 →
    ∀ row, addresses.intToPtrMap[cut-1]? = some row →
      GlobalAddressLiveErrorExclusion.Supplier memory row.allocId
  targets : ∀ row ∈ addresses.intToPtrMap, SelectedRow memory addresses address row →
    addresses.exposed.contains row.allocId = true → TargetMetadata context memory addresses row.allocId none

/-- Query-local data supplies the existing internal miss/hit dispatch.
No selected resolver result or successful retag is a hypothesis. -/
theorem classify {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64)
    (input : Query context memory addresses address) :
    addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) = .ok none ∨
      Nonempty (Hit context memory addresses address) := by
  rcases CurrentCallEmptyQueryMetadata.classify memory addresses address input.coherent input.nonstrict input.predecessor with
    ⟨position,row,valid,present,equal,done⟩ | ⟨cut,partition,choice⟩
  · by_cases exposed : addresses.exposed.contains row.allocId = true
    · have member := Array.mem_of_getElem? present
      have target := input.targets row member (Or.inl equal) exposed
      obtain ⟨info,known⟩ := target_metadata_known context memory addresses row.allocId none target
      exact Or.inr ⟨⟨row.allocId,row.address,info,known,Or.inl ⟨equal.symm,position,valid,input.coherent.ordered,present⟩,
        exposed,input.cached row member,target⟩⟩
    · change addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) =
        .ok (if addresses.exposed.contains row.allocId = true then some row.allocId else none) at done
      rw [ite_eq_right exposed] at done
      exact Or.inl done
  · rcases choice with ⟨zero,done⟩ | ⟨row,info,nonzero,present,known,nondead,done⟩
    · exact Or.inl done
    · by_cases inside : address-row.address < info.size.bytes ∧ addresses.exposed.contains row.allocId = true
      · have member := Array.mem_of_getElem? present
        have position : cut-1+1 = cut := by omega
        have target := input.targets row member (Or.inr ⟨cut,info,partition,nonzero,present,known,inside.1⟩) inside.2
        exact Or.inr ⟨⟨row.allocId,row.address,info,known,
          Or.inr ⟨cut-1,by rw [position];exact partition,present,inside.1⟩,
          inside.2,input.cached row member,target⟩⟩
      · rw [ite_eq_right inside] at done
        exact Or.inl done

/-- The image/profile envelope is bound to the actual pinned compiler image,
runtime extras, tracker root cache and native-path configuration. -/
theorem actual {options : EvalConfigurationCore.Options} {before : Before}
    (tracker : MachineHooks.BorrowState) (address : UInt64)
    (input : Query (imageContext options before tracker) before.memory before.user.addresses address) :
    before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none ∨
      Nonempty (Hit (imageContext options before tracker) before.memory before.user.addresses address) :=
  classify _ _ _ _ input

end
end DuplicatePrefix.CurrentCallEmptySelectedHit

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptySelectedHit" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved selected empty hit dependency {dependency}"
