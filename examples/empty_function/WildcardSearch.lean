import empty_function.InputDraft
import Miri.Interpreter.TypedMemoryProviders
import Lean

/-! Source inverse-search partition for zero-byte wildcard resolution.
The loop proofs follow the source inverse search directly.
No alternate search or operation-success premise. -/
namespace EmptyFunction.WildcardSearch
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open Lean Elab Meta Tactic in
private def helper (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (n,_) =>
    if n.toString.endsWith suffix then some n else none
  match names with
  | [name] => pure name
  | _ => throwError "expected one source helper {suffix}"
open Lean Elab in
elab "source_inverse" : term => do
  Meta.mkConstWithFreshMVarLevels (← helper ".findInverseIndex")
open Lean Elab Tactic in
elab "unfold_inverse" : tactic => do
  let n := mkIdent (← helper ".findInverseIndex")
  evalTactic (← `(tactic| unfold $n:ident))
open Lean Elab Meta Tactic in
elab "name_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun e => e.isAppOf ``Lean.Loop.forIn)
      | throwError "no source loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← inferType body) body
    let (scan,goal) ← goal.intro1P
    return [← goal.change (target.replace fun e => if e == body then some (mkFVar scan) else none)]
private theorem loop_finished {β : Type} (scan : Unit → β → Id (ForInStep β))
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

def Ordered (entries : Array InverseAddressEntry) : Prop :=
  ∀ left right (lt : left < right) (valid : right < entries.size), entries[left].address < entries[right].address

def Cut (entries : Array InverseAddressEntry) (address : UInt64) (cut : Nat) : Prop :=
  cut ≤ entries.size ∧
  (∀ i (valid : i < entries.size), i < cut → entries[i].address < address) ∧
  (∀ i (valid : i < entries.size), cut ≤ i → address < entries[i].address)
theorem inverse_hit (entries : Array InverseAddressEntry) (base : UInt64) (id : AllocId)
    (position : Nat) (valid : position < entries.size) (ordered : Ordered entries)
    (row : entries[position]? = some ⟨base,id⟩) :
    source_inverse entries base = (position,true) := by
  have actual : entries[position] = ⟨base,id⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  unfold_inverse
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧
    match state.2.2 with
    | none => state.1 ≤ position ∧ position < state.2.1
    | some found => found = position
  let final : (Nat × Nat × Option Nat) → Prop := fun state => state.2.2 = some position
  let measure : (Nat × Nat × Option Nat) → Nat := fun state =>
    if state.2.2.isNone then state.2.1-state.1+1 else 0
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ measure next < measure state := by
    intro state good
    rcases state with ⟨low,high,found⟩
    rcases good with ⟨order,bounded,selection⟩
    dsimp only at order bounded selection
    cases found with
    | some found =>
      subst found
      exact Or.inl ⟨(low,high,some position),by simp [scan],rfl⟩
    | none =>
      have nonempty : low < high := by omega
      let middle := low+(high-low)/2
      have lower : low ≤ middle := by omega
      have upper : middle < high := by omega
      have middleValid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem middleValid
      rcases Nat.lt_trichotomy middle position with earlier | same | later
      · have before := ordered middle position earlier valid
        rw [actual] at before
        change entries[middle].address < base at before
        refine Or.inr ⟨(middle+1,high,none),?_,?_,?_⟩
        · simp [scan,nonempty,middle,lookup,before]
        · change middle+1 ≤ high ∧ high ≤ entries.size ∧ middle+1 ≤ position ∧ position < high
          omega
        · change high-(middle+1)+1 < high-low+1
          omega
      · have equal : entries[middle].address = base := by
          simpa only [same] using congrArg InverseAddressEntry.address actual
        refine Or.inr ⟨(low,high,some middle),?_,?_,?_⟩
        · simp [scan,nonempty,middle,lookup,equal]
        · exact ⟨order,bounded,same⟩
        · change 0 < high-low+1
          omega
      · have after := ordered position middle later middleValid
        rw [actual] at after
        change base < entries[middle].address at after
        have notBefore : ¬ entries[middle].address < base := by
          have greater := UInt64.lt_iff_toNat_lt.mp after
          intro before
          have less := UInt64.lt_iff_toNat_lt.mp before
          omega
        refine Or.inr ⟨(low,middle,none),?_,?_,?_⟩
        · simp [scan,nonempty,middle,lookup,notBefore,after]
        · change low ≤ middle ∧ middle ≤ entries.size ∧ low ≤ position ∧ position < middle
          omega
        · change middle-low+1 < high-low+1
          omega
  have finished := loop_finished scan measure invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,Nat.le_refl _,Nat.zero_le _,valid⟩
  simp only [final] at finished
  simp [finished]
theorem inverse_cut (entries : Array InverseAddressEntry) (address : UInt64)
    (ordered : Ordered entries) (different : ∀ row ∈ entries, row.address ≠ address) :
    ∃ cut, source_inverse entries address = (cut,false) ∧ Cut entries address cut := by
  unfold_inverse
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_scan
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
  have result := loop_finished scan (fun state => state.2.1-state.1) invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,Nat.le_refl _,rfl,by intro index valid impossible;change index < 0 at impossible;omega,by intro index valid impossible;change entries.size ≤ index at impossible;omega⟩
  refine ⟨_,?_,?_,result.2.2.2.1,result.2.2.2.2⟩
  · simp [result.2.2.1]
  · exact result.1 ▸ result.2.1

/-- Exhaustive raw geometry classification of the actual ordered inverse
search: an exact row, or an insertion partition. This is independent of all
allocation metadata and is not a disjunction defined to be validity. -/
theorem inverse_partition (entries : Array InverseAddressEntry) (address : UInt64) (ordered : Ordered entries) :
    (∃ position row, position < entries.size ∧ entries[position]? = some row ∧ row.address = address ∧
      source_inverse entries address = (position,true)) ∨
    ∃ cut, source_inverse entries address = (cut,false) ∧ Cut entries address cut := by
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
      exact inverse_hit entries address row.allocId position valid ordered raw
  · apply Or.inr
    apply inverse_cut entries address ordered
    intro row member same
    exact exactRow ⟨row,member,same⟩

end EmptyFunction.WildcardSearch
