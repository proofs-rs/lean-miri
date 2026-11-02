import Miri.Memory.AllocAddresses.GlobalState
import Lean
namespace EmptyFunction.RawAddressCache
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def helper (suffix : String) : TermElabM Name := do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  let [name] := found | throwError "expected one source definition {suffix}"
  return name
elab "actual_source_search" : term => return mkConst (← helper ".GlobalAddressState.findInverseIndex")
elab "unfold_source_search" : tactic => do
  let name ← helper ".GlobalAddressState.findInverseIndex"
  evalTactic (← `(tactic| unfold $(mkIdent name)))
elab "unfold_source_base" : tactic => do
  let name ← helper ".GlobalAddressState.findBase"
  evalTactic (← `(tactic| unfold $(mkIdent name)))
elab "unfold_source_generation" : tactic => do
  let name ← helper ".GlobalAddressState.setGeneration"
  evalTactic (← `(tactic| unfold $(mkIdent name)))
abbrev sourceSearch : Array InverseAddressEntry → UInt64 → Nat × Bool := actual_source_search
elab "name_range_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``Lean.Loop.forIn)
      | throwError "no Loop.forIn found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan, goal) ← goal.intro1P
    let target ← goal.getType
    let target := target.replace fun expr =>
      if expr == body then some (mkFVar scan) else none
    return [← goal.change target]

theorem loop_finished {β : Type} (scan : Unit → β → Id (ForInStep β))
    (measure : β → Nat) (invariant final : β → Prop)
    (step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ measure next < measure state)
    (initial : β) (valid : invariant initial) : final (Lean.Loop.forIn {} initial scan) := by
  have sound : ∀ bound state, measure state = bound → invariant state → final (Lean.Loop.forIn {} state scan) := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with done | more
      · obtain ⟨last,actual,finished⟩ := done
        simpa only [actual,bind,pure] using finished
      · obtain ⟨next,actual,preserved,smaller⟩ := more
        simp only [actual,bind]
        exact ih (measure next) (by omega) next rfl preserved
  exact sound (measure initial) initial rfl valid

def Cut (entries : Array InverseAddressEntry) (address : UInt64) (cut : Nat) : Prop :=
  cut ≤ entries.size ∧
  (∀ index (valid : index < entries.size), index < cut → entries[index].address < address) ∧
  (∀ index (valid : index < entries.size), cut ≤ index → address < entries[index].address)

/-- The unchanged source binary search computes the insertion position from
the initial vector's raw address partition, for arbitrary finite vector length. -/
theorem inverse_cut (entries : Array InverseAddressEntry) (address : UInt64) (cut : Nat)
    (geometry : Cut entries address cut) :
    sourceSearch entries address = (cut,false) := by
  unfold sourceSearch
  unfold_source_search
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ cut ∧ cut ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧ state.2.2 = none
  let final : (Nat × Nat × Option Nat) → Prop := fun state => state.1 = cut ∧ state.2.2 = none
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ state.2.1-state.1 > next.2.1-next.1 := by
    intro state good
    rcases state with ⟨low,high,found⟩
    rcases good with ⟨lowCut,cutHigh,bounded,missing⟩
    dsimp only at lowCut cutHigh bounded missing
    subst found
    by_cases nonempty : low < high
    · let middle := low+(high-low)/2
      have lower : low ≤ middle := by omega
      have upper : middle < high := by omega
      have valid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem valid
      by_cases before : middle < cut
      · have earlier := geometry.2.1 middle valid before
        refine Or.inr ⟨(middle+1,high,none),?_,⟨by change middle+1 ≤ cut;omega,cutHigh,bounded,rfl⟩,?_⟩
        · simp [scan,nonempty,middle,lookup,earlier]
        · change high-low > high-(middle+1);omega
      · have later := geometry.2.2 middle valid (by omega)
        have notEarlier : ¬ entries[middle].address < address := by
          have greater := UInt64.lt_iff_toNat_lt.mp later
          intro earlier
          have less := UInt64.lt_iff_toNat_lt.mp earlier
          omega
        refine Or.inr ⟨(low,middle,none),?_,⟨lowCut,by change cut ≤ middle;omega,by change middle ≤ entries.size;omega,rfl⟩,?_⟩
        · simp [scan,nonempty,middle,lookup,notEarlier,later]
        · change high-low > middle-low;omega
    · refine Or.inl ⟨(low,high,none),by simp [scan,nonempty],by change low = cut;omega,rfl⟩
  have finished := loop_finished scan (fun state => state.2.1-state.1) invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,geometry.1,Nat.le_refl _,rfl⟩
  simp only [final] at finished
  simp [finished.1,finished.2]


/-- A fresh bump lies after every current indexed base. The unchanged source
search therefore inserts at the end, without assuming cache success. -/
theorem cache_after (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0)
    (afterAll : ∀ row ∈ state.intToPtrMap, row.address < address) :
    (state.cacheAddress id address).outcome = .ok () := by
  have search := inverse_cut state.intToPtrMap address state.intToPtrMap.size
    ⟨Nat.le_refl _, by intro i valid _; exact afterAll _ (Array.getElem_mem valid),
      by intro i valid outside; omega⟩
  unfold GlobalAddressState.cacheAddress
  unfold_source_base
  simp only [uncached, Option.map_none, show (address == 0) = false from by simpa using nonzero,
    Bool.false_eq_true, ↓reduceIte, sourceSearch] at *
  rw [search]
  simp

/-- Address uniqueness alone gives a bounded source insertion index. This
covers reused holes as well as fresh bumps, without requiring an empty map. -/
theorem inverse_absent (entries : Array InverseAddressEntry) (address : UInt64)
    (different : ∀ row ∈ entries, row.address ≠ address) :
    ∃ position, sourceSearch entries address = (position,false) ∧ position ≤ entries.size := by
  unfold sourceSearch
  unfold_source_search
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧ state.2.2 = none
  let final : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ entries.size ∧ state.2.2 = none
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ next.2.1-next.1 < state.2.1-state.1 := by
    intro state good
    rcases state with ⟨low,high,found⟩
    rcases good with ⟨ordered,bounded,missing⟩
    dsimp only at ordered bounded missing
    subst found
    by_cases nonempty : low < high
    · let middle := low+(high-low)/2
      have atLeast : low ≤ middle := by omega
      have before : middle < high := by omega
      have valid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem valid
      have distinct := different entries[middle] (Array.getElem_mem valid)
      by_cases earlier : entries[middle].address < address
      · refine Or.inr ⟨(middle+1,high,none),?_,⟨by change middle+1 ≤ high;omega,bounded,rfl⟩,?_⟩
        · simp [scan,nonempty,middle,lookup,earlier]
        · change high-(middle+1)<high-low;omega
      · have later : address < entries[middle].address := by
          apply UInt64.lt_iff_toNat_lt.mpr
          have ne : entries[middle].address.toNat ≠ address.toNat := fun equal => distinct (UInt64.toNat_inj.mp equal)
          have notEarlier : ¬entries[middle].address.toNat < address.toNat := by simpa only [UInt64.lt_iff_toNat_lt] using earlier
          omega
        refine Or.inr ⟨(low,middle,none),?_,⟨atLeast,by change middle ≤ entries.size;omega,rfl⟩,?_⟩
        · simp [scan,nonempty,middle,lookup,earlier,later]
        · change middle-low<high-low;omega
    · refine Or.inl ⟨(low,high,none),by simp [scan,nonempty],?_,rfl⟩
      change low ≤ entries.size
      omega
  have finished := loop_finished scan (fun state => state.2.1-state.1) invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,Nat.le_refl _,rfl⟩
  exact ⟨_,by simp [finished.2],finished.1⟩

theorem cache_fresh (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (different : ∀ row ∈ state.intToPtrMap, row.address ≠ address) :
    (state.cacheAddress id address).outcome = .ok () := by
  obtain ⟨position,search,bounded⟩ := inverse_absent state.intToPtrMap address different
  unfold GlobalAddressState.cacheAddress
  unfold_source_base
  simp only [uncached,Option.map_none,sourceSearch] at *
  split
  · rfl
  · simp only [search,Bool.false_eq_true,↓reduceIte,bounded,↓reduceDIte]
    rfl

end EmptyFunction.RawAddressCache

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.RawAddressCache." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved raw address proof axiom {dependency} in {name}"
