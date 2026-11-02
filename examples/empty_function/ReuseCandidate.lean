import empty_function.RawAddressCache
namespace EmptyFunction.ReuseCandidate
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Lean Elab Tactic
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def helper (suffix : String) : TermElabM Name := do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  let [name] := found | throwError "expected one source definition {suffix}"
  return name
elab "actual_candidate" : term => return mkConst (←helper ".ReusePool.candidateRange")
elab "unfold_candidate" : tactic => do
  let name ← helper ".ReusePool.candidateRange"
  evalTactic (← `(tactic| unfold $(mkIdent name)))
elab "actual_entry" : term => return mkConst (←helper ".ReusePool.entryAt?")

elab "actual_partition" : term => return mkConst (←helper ".ReusePool.partitionPoint")
abbrev partition : Array ReusableAddress → (ReusableAddress → Bool) → Nat := actual_partition

abbrev candidate : Array ReusableAddress → Size → AddressThreadId → Bool → Nat × Nat := actual_candidate

def Matches (entry : ReusableAddress) (size : Size) (thread : AddressThreadId) (cross : Bool) : Prop :=
  entry.size.bytes = size.bytes ∧ (cross = false → entry.thread = thread)

/-- The selected source range contains only actual same-size/thread entries.
This does not rely on global pool sortedness or a successful take operation. -/
theorem range_spec (entries : Array ReusableAddress) (size : Size)
    (thread : AddressThreadId) (cross : Bool) :
    (candidate entries size thread cross).1 ≤ (candidate entries size thread cross).2 ∧
    ∀ selected, (candidate entries size thread cross).1 ≤ selected →
      selected < (candidate entries size thread cross).2 →
      ∃ valid : selected < entries.size, Matches entries[selected] size thread cross := by
  unfold candidate
  unfold_candidate
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let begin := partition entries (fun entry => entry.size.bytes < size.bytes ||
    (entry.size.bytes == size.bytes && !cross && entry.thread < thread))
  let limit := max begin entries.size
  let invariant : Nat × Bool → Prop := fun state =>
    begin ≤ state.1 ∧ state.1 ≤ limit ∧
      ∀ selected, begin ≤ selected → selected < state.1 →
        ∃ valid : selected < entries.size, Matches entries[selected] size thread cross
  let final : Nat × Bool → Prop := fun state =>
    begin ≤ state.1 ∧ ∀ selected, begin ≤ selected → selected < state.1 →
      ∃ valid : selected < entries.size, Matches entries[selected] size thread cross
  let measure : Nat × Bool → Nat := fun state => if state.2 then limit-state.1+1 else 0
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ measure next < measure state := by
    intro state good
    rcases state with ⟨stop,running⟩
    obtain ⟨lower,upper,rows⟩ := good
    cases running with
    | false => exact .inl ⟨(stop,false),by simp [scan],lower,rows⟩
    | true =>
      have unchanged : invariant (stop,false) := ⟨lower,upper,rows⟩
      have decreased : measure (stop,false) < measure (stop,true) := by simp [measure]
      have entryDef : actual_entry entries stop = entries[stop]? := rfl
      cases lookup : entries[stop]? with
      | none =>
        exact .inr ⟨(stop,false),by dsimp only [scan]; rw [entryDef]; simp [lookup],unchanged,decreased⟩
      | some entry =>
        by_cases bad : (entry.size.bytes != size.bytes || !cross && entry.thread != thread) = true
        · exact .inr ⟨(stop,false),by dsimp only [scan]; rw [entryDef]; simp [lookup,bad],unchanged,decreased⟩
        · obtain ⟨valid,equal⟩ := Array.getElem?_eq_some_iff.mp lookup
          have matched : Matches entry size thread cross := by
            unfold Matches
            cases cross <;> simp_all
          have nextGood : invariant (stop+1,true) := by
            refine ⟨by change begin ≤ stop+1;omega,?_,?_⟩
            · change stop+1 ≤ limit
              have maxBound : entries.size ≤ limit := Nat.le_max_right _ _
              omega
            · intro selected lowerSelected upperSelected
              by_cases old : selected < stop
              · exact rows selected lowerSelected old
              · have same : selected = stop := by change selected < stop+1 at upperSelected; omega
                subst selected
                exact ⟨valid,by simpa only [equal] using matched⟩
          refine .inr ⟨(stop+1,true),?_,nextGood,?_⟩
          · dsimp only [scan]; rw [entryDef]; simp [lookup,bad]
          · dsimp only [measure]
            simp only [↓reduceIte]
            change limit-(stop+1)+1 < limit-stop+1
            have maxBound : entries.size ≤ limit := Nat.le_max_right _ _
            omega
  have finished := RawAddressCache.loop_finished scan measure invariant final step
    (begin,true) ⟨Nat.le_refl _,Nat.le_max_left _ _,by intro selected lower upper;omega⟩
  exact finished

theorem selected (entries : Array ReusableAddress) (size : Size)
    (thread : AddressThreadId) (cross : Bool) :
    ∀ selected, (candidate entries size thread cross).1 ≤ selected →
      selected < (candidate entries size thread cross).2 →
      ∃ valid : selected < entries.size, Matches entries[selected] size thread cross :=
  (range_spec entries size thread cross).2

theorem empty (size : Size) (thread : AddressThreadId) (cross : Bool) :
    (candidate #[] size thread cross).2 = (candidate #[] size thread cross).1 := by
  have spec := range_spec #[] size thread cross
  have notStrict : ¬ (candidate #[] size thread cross).1 < (candidate #[] size thread cross).2 := by
    intro strict
    obtain ⟨valid,_⟩ := spec.2 (candidate #[] size thread cross).1 (Nat.le_refl _) strict
    simp at valid
  omega
end EmptyFunction.ReuseCandidate
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ReuseCandidate.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reuse candidate axiom {dependency} in {name}"
