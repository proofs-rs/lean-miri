import duplicate_prefix.WildcardEmptyAddressClassification

/-! Query-local coverage of the actual zero-byte wildcard resolver.
This module does not supply later pointer conversion, cached-base coherence,
lazy-image materialization, or typed empty-reference entry data. Deriving those
from ordinary input remains OPEN; metadata coverage alone is not admission. -/
namespace DuplicatePrefix.CurrentCallEmptyQueryMetadata
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open WildcardInteriorHitAddress (Ordered Cut)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Query-local source classification from actual ordered/coherent address rows
and query-local raw memory metadata suppliers. Exact hits skip size queries. Missing exact
hits select only the immediate predecessor, whose real size and exposure decide
the result. No successful lookup or preselected invocation family is supplied. -/
theorem classify {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (address : UInt64)
    (coherent : GlobalAddressRecurringFormation.State memory addresses)
    (nonstrict : addresses.provenanceMode ≠ .strict)
    (metadata : ∀ cut, Cut addresses.intToPtrMap address cut → cut ≠ 0 →
      ∀ row, addresses.intToPtrMap[cut-1]? = some row →
        GlobalAddressLiveErrorExclusion.Supplier memory row.allocId) :
    let hooks := GlobalAddressLiveErrorExclusion.lookup memory
    (∃ position row, position < addresses.intToPtrMap.size ∧
      addresses.intToPtrMap[position]? = some row ∧ row.address = address ∧
      addresses.allocIdFromAddr address 0 hooks = .ok (if addresses.exposed.contains row.allocId then some row.allocId else none)) ∨
    ∃ cut, Cut addresses.intToPtrMap address cut ∧
      ((cut = 0 ∧ addresses.allocIdFromAddr address 0 hooks = .ok none) ∨
       ∃ row info, cut ≠ 0 ∧ addresses.intToPtrMap[cut-1]? = some row ∧
         memory.getAllocInfo row.allocId = .ok info ∧ info.kind ≠ .dead ∧
         addresses.allocIdFromAddr address 0 hooks = .ok
           (if address-row.address < info.size.bytes ∧ addresses.exposed.contains row.allocId = true then some row.allocId else none)) := by
  dsimp only
  rcases WildcardEmptyAddressClassification.inverse_partition addresses.intToPtrMap address coherent.ordered with
    ⟨position,row,valid,present,equal,search⟩ | ⟨cut,search,partition⟩
  · apply Or.inl
    refine ⟨position,row,valid,present,equal,?_⟩
    have live := coherent.live.1 row (Array.mem_of_getElem? present)
    unfold GlobalAddressState.allocIdFromAddr
    unfold_global_data ".GlobalAddressState.inverseSearch"
    cases exposed : addresses.exposed.contains row.allocId <;>
      simp [nonstrict,search,present,GlobalAddressLiveErrorExclusion.lookup,live,
        bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] <;> simpa using exposed
  · apply Or.inr
    refine ⟨cut,partition,?_⟩
    by_cases zero : cut = 0
    · apply Or.inl
      refine ⟨zero,?_⟩
      unfold GlobalAddressState.allocIdFromAddr
      unfold_global_data ".GlobalAddressState.inverseSearch"
      simp [nonstrict,search,zero,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
    · apply Or.inr
      have valid : cut-1 < addresses.intToPtrMap.size := by have bounded := partition.1;omega
      let row := addresses.intToPtrMap[cut-1]
      have present : addresses.intToPtrMap[cut-1]? = some row := Array.getElem?_eq_getElem valid
      obtain ⟨info,known,nondead⟩ := GlobalAddressLiveErrorExclusion.metadata_of_supplier memory row.allocId
        (metadata cut partition zero row present)
      refine ⟨row,info,zero,present,known,nondead,?_⟩
      have live := coherent.live.1 row (Array.getElem_mem valid)
      unfold GlobalAddressState.allocIdFromAddr
      unfold_global_data ".GlobalAddressState.inverseSearch"
      by_cases inside : address-row.address < info.size.bytes
      all_goals cases exposed : addresses.exposed.contains row.allocId <;>
        simp [nonstrict,search,zero,present,inside,GlobalAddressLiveErrorExclusion.lookup,known,live,
          bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Except.toOption] <;> simp_all

/-- A zero-byte wildcard allocation lookup completes using metadata only for
the immediate predecessor of this query. Exact hits require no size metadata. Later pointer conversion/retagging
still has its separate base-cache, global-materialization and TB contracts. -/
theorem total {Prov Extra K : Type} (memory : MemoryState Prov Extra K)
    (addresses : GlobalAddressState) (address : UInt64)
    (coherent : GlobalAddressRecurringFormation.State memory addresses)
    (nonstrict : addresses.provenanceMode ≠ .strict)
    (metadata : ∀ cut, Cut addresses.intToPtrMap address cut → cut ≠ 0 →
      ∀ row, addresses.intToPtrMap[cut-1]? = some row →
        GlobalAddressLiveErrorExclusion.Supplier memory row.allocId) :
    ∃ result, addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) = .ok result := by
  rcases classify memory addresses address coherent nonstrict metadata with
    ⟨position,row,valid,present,equal,done⟩ | ⟨cut,partition,choice⟩
  · exact ⟨_,done⟩
  · rcases choice with ⟨zero,done⟩ | ⟨row,info,positive,present,known,nondead,done⟩
    · exact ⟨_,done⟩
    · exact ⟨_,done⟩

end DuplicatePrefix.CurrentCallEmptyQueryMetadata

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyQueryMetadata" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved query-local metadata dependency {dependency}"
