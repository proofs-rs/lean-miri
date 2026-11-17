import Miri.TreeBorrows.UniMap
import duplicate_prefix.RangeMapNonempty
import duplicate_prefix.GeneralBorrowLoop
namespace DuplicatePrefix.GeneralBorrowTrimLookup
open Miri.TreeBorrows
open DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem pop_none {α : Type} (data : Array (Option α)) (query : UniIndex)
    (back : data.back? = some none) :
    (UniValMap.get ⟨data.pop⟩ query) = (UniValMap.get ⟨data⟩ query) := by
  obtain ⟨trimmed,equal⟩ := Array.back?_eq_some_iff.mp back
  subst data
  simp only [Array.pop_push,UniValMap.get,Array.getElem?_push]
  by_cases bounded : query.toNat < trimmed.size
  · simp [bounded,Nat.ne_of_lt bounded]
  · have absent : trimmed[query.toNat]? = none := Array.getElem?_eq_none (by omega)
    simp only [bounded,↓reduceIte,absent]
    by_cases equal : query.toNat = trimmed.size <;> simp [equal]

/-- Production trimming removes only trailing absent slots; all sparse lookups survive. -/
theorem trim_get {α : Type} (map : UniValMap α) (query : UniIndex) :
    map.trimTrailingNone.get query = map.get query := by
  unfold UniValMap.trimTrailingNone
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  let property := fun data : Array (Option α) => UniValMap.get ⟨data⟩ query = map.get query
  have step : ∀ data, property data →
      (∃ final, scan () data = .done final ∧ property final) ∨
      ∃ next, scan () data = .yield next ∧ property next ∧ next.size < data.size := by
    intro data good
    cases back : data.back? with
    | none => exact .inl ⟨data,by simp [scan,back],good⟩
    | some value =>
      cases value with
      | some value => exact .inl ⟨data,by simp [scan,back],good⟩
      | none =>
        refine .inr ⟨data.pop,by simp [scan,back],(pop_none data query back).trans good,?_⟩
        obtain ⟨trimmed,equal⟩ := Array.back?_eq_some_iff.mp back
        rw [equal]
        simp
  exact GeneralBorrowLoop.invariant scan Array.size property step map.data rfl
end DuplicatePrefix.GeneralBorrowTrimLookup
