import duplicate_prefix.WildcardOrderedHitAddress
import duplicate_prefix.WildcardMetadataGap
import duplicate_prefix.GlobalAddressLiveErrorExclusion

namespace DuplicatePrefix.WildcardEmptyAddressClassification
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open WildcardInteriorHitAddress (Ordered Cut)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- An actual ordered inverse vector without an exact target has a source
binary-search insertion partition. No search result or family membership is
supplied as an input. -/
theorem inverse_cut (entries : Array InverseAddressEntry) (address : UInt64)
    (ordered : Ordered entries) (different : ∀ row ∈ entries, row.address ≠ address) :
    ∃ cut, miss_source_inverse_search entries address = (cut,false) ∧ Cut entries address cut := by
  unfold_global_data ".findInverseIndex"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧ state.2.2 = none ∧
    (∀ index (valid : index < entries.size), index < state.1 → entries[index].address < address) ∧
    (∀ index (valid : index < entries.size), state.2.1 ≤ index → address < entries[index].address)
  let final : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 = state.2.1 ∧ state.2.1 ≤ entries.size ∧ state.2.2 = none ∧
    (∀ index (valid : index < entries.size), index < state.1 → entries[index].address < address) ∧
    (∀ index (valid : index < entries.size), state.1 ≤ index → address < entries[index].address)
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ next.2.1-next.1 < state.2.1-state.1 := by
    intro state good
    rcases state with ⟨low,high,found⟩
    obtain ⟨order,bounded,missing,lower,upper⟩ := good
    dsimp only at order bounded missing lower upper
    subst found
    by_cases nonempty : low < high
    · let middle := low+(high-low)/2
      have atLeast : low ≤ middle := by omega
      have before : middle < high := by omega
      have valid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem valid
      have distinct := different entries[middle] (Array.getElem_mem valid)
      by_cases earlier : entries[middle].address < address
      · refine Or.inr ⟨(middle+1,high,none),?_,?_,by change high-(middle+1)<high-low;omega⟩
        · simp [scan,nonempty,middle,lookup,earlier]
        · refine ⟨by change middle+1≤high;omega,bounded,rfl,?_,upper⟩
          intro index indexValid below
          change index < middle+1 at below
          by_cases same : index = middle
          · subst index; exact earlier
          · have beforeMiddle : index < middle := by omega
            have sorted := ordered index middle beforeMiddle valid
            exact UInt64.lt_iff_toNat_lt.mpr (by
              have one := UInt64.lt_iff_toNat_lt.mp sorted
              have two := UInt64.lt_iff_toNat_lt.mp earlier
              omega)
      · have later : address < entries[middle].address := by
          apply UInt64.lt_iff_toNat_lt.mpr
          have ne : entries[middle].address.toNat ≠ address.toNat := fun equal => distinct (UInt64.toNat_inj.mp equal)
          have notEarlier : ¬entries[middle].address.toNat < address.toNat := by simpa only [UInt64.lt_iff_toNat_lt] using earlier
          omega
        refine Or.inr ⟨(low,middle,none),?_,?_,by change middle-low<high-low;omega⟩
        · simp [scan,nonempty,middle,lookup,earlier,later]
        · refine ⟨atLeast,by change middle≤entries.size;omega,rfl,lower,?_⟩
          intro index indexValid above
          change middle ≤ index at above
          by_cases same : index = middle
          · subst index; exact later
          · have afterMiddle : middle < index := by omega
            have sorted := ordered middle index afterMiddle indexValid
            exact UInt64.lt_iff_toNat_lt.mpr (by
              have one := UInt64.lt_iff_toNat_lt.mp later
              have two := UInt64.lt_iff_toNat_lt.mp sorted
              omega)
    · have equal : low = high := by omega
      refine Or.inl ⟨(low,high,none),by simp [scan,nonempty],equal,bounded,rfl,lower,?_⟩
      intro index valid above
      exact upper index valid (by omega)
  have result := GeneralRangeMapFind.loop_finished scan (fun state => state.2.1-state.1) invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,Nat.le_refl _,rfl,by intro index valid impossible;change index < 0 at impossible;omega,by intro index valid impossible;change entries.size ≤ index at impossible;omega⟩
  refine ⟨_,?_,?_,result.2.2.2.1,result.2.2.2.2⟩
  · simp [result.2.2.1]
  · exact result.1 ▸ result.2.1

/-- Exhaustive raw geometry classification of the actual ordered inverse
search: an exact row, or an insertion partition. This is independent of all
allocation metadata and is not a disjunction defined to be validity. -/
theorem inverse_partition (entries : Array InverseAddressEntry) (address : UInt64) (ordered : Ordered entries) :
    (∃ position row, position < entries.size ∧ entries[position]? = some row ∧ row.address = address ∧
      miss_source_inverse_search entries address = (position,true)) ∨
    ∃ cut, miss_source_inverse_search entries address = (cut,false) ∧ Cut entries address cut := by
  by_cases exactRow : ∃ row ∈ entries, row.address = address
  · obtain ⟨row,member,equal⟩ := exactRow
    obtain ⟨position,valid,lookup⟩ := Array.mem_iff_getElem.mp member
    apply Or.inl
    refine ⟨position,row,valid,?_,equal,?_⟩
    · simpa only [lookup] using Array.getElem?_eq_getElem valid
    · have shape : row = ⟨address,row.allocId⟩ := by
        cases row with
        | mk rowAddress id => cases equal; rfl
      have raw : entries[position]? = some ⟨address,row.allocId⟩ :=
        (Array.getElem?_eq_getElem valid).trans (congrArg some (lookup.trans shape))
      exact WildcardOrderedHitAddress.inverse_hit entries address row.allocId position valid ordered raw
  · apply Or.inr
    apply inverse_cut entries address ordered
    intro row member same
    exact exactRow ⟨row,member,same⟩

end DuplicatePrefix.WildcardEmptyAddressClassification
