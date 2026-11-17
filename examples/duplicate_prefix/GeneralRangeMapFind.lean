import duplicate_prefix.GeneralRangeMapGeometry
import duplicate_prefix.GeneralBorrowLoop
namespace DuplicatePrefix.GeneralRangeMapFind
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapGeometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
abbrev State := Nat × Nat × Option (Except DedupRangeMapError Nat)
def Invariant (map : DedupRangeMap α) (offset : UInt64) (state : State) : Prop :=
  state.1 ≤ state.2.1 ∧ state.2.1 ≤ map.entries.size ∧
  match state.2.2 with
  | none => ∃ index, state.1 ≤ index ∧ index < state.2.1 ∧ Contains map offset index
  | some (.ok index) => Contains map offset index
  | some (.error _) => False
def Finished (map : DedupRangeMap α) (offset : UInt64) (state : State) : Prop :=
  ∃ index, state.2.2 = some (.ok index) ∧ Contains map offset index
def measure (state : State) : Nat := if state.2.2.isNone then state.2.1-state.1+1 else 0

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

theorem find_success (map : DedupRangeMap α) (offset : UInt64)
    (good : map.WellFormed) (inside : offset.toNat < map.size.bytes.toNat) :
    ∃ index, range_find_offset map offset = .ok index ∧ Contains map offset index := by
  have covered := GeneralRangeMapGeometry.covered map good offset inside
  simp_range_helpers
  name_range_scan
  have step : ∀ state, Invariant map offset state →
      (∃ done, scan () state = .done done ∧ Finished map offset done) ∨
      ∃ next, scan () state = .yield next ∧ Invariant map offset next ∧ measure next < measure state := by
    intro state valid
    rcases state with ⟨low,high,answer⟩
    dsimp only [Invariant] at valid
    rcases valid with ⟨ordered,bounded,payload⟩
    cases answer with
    | some answer =>
      cases answer with
      | error error => exact False.elim payload
      | ok index =>
        exact .inl ⟨(low,high,some (.ok index)),by simp [scan],index,rfl,payload⟩
    | none =>
      obtain ⟨target,lower,upper,targetValid,targetStart,targetStop⟩ := payload
      have nonempty : low < high := by omega
      let middle := low+(high-low)/2
      have middleLow : low ≤ middle := by omega
      have middleHigh : middle < high := by omega
      have middleValid : middle < map.entries.size := by omega
      by_cases before : offset < map.entries[middle].range.start
      · have beforeNat := UInt64.lt_iff_toNat_lt.mp before
        have targetBefore : target < middle := by
          by_cases same : target = middle
          · subst target
            omega
          by_cases earlier : middle < target
          · have between := stop_le_start map good middle target earlier targetValid
            have positive := (facts map good (by omega)).2.1 middle middleValid
            omega
          · omega
        refine .inr ⟨(low,middle,none),?_,?_,?_⟩
        · simp [scan,middle,middleValid,before,nonempty]
        · dsimp only [Invariant]
          exact ⟨middleLow,by omega,target,lower,targetBefore,targetValid,targetStart,targetStop⟩
        · change middle-low+1 < high-low+1
          omega
      · by_cases after : offset ≥ map.entries[middle].range.stop
        · have afterNat := UInt64.le_iff_toNat_le.mp after
          have middleBefore : middle < target := by
            by_cases same : target = middle
            · subst target
              omega
            by_cases earlier : target < middle
            · have between := stop_le_start map good target middle earlier middleValid
              have positive := (facts map good (by omega)).2.1 middle middleValid
              omega
            · omega
          refine .inr ⟨(middle+1,high,none),?_,?_,?_⟩
          · simp [scan,middle,middleValid,before,after,nonempty]
          · dsimp only [Invariant]
            exact ⟨by omega,bounded,target,by omega,upper,targetValid,targetStart,targetStop⟩
          · change high-(middle+1)+1 < high-low+1
            omega
        · have starts : map.entries[middle].range.start.toNat ≤ offset.toNat := by
            simp only [UInt64.lt_iff_toNat_lt] at before
            omega
          have stops : offset.toNat < map.entries[middle].range.stop.toNat := by
            simp only [ge_iff_le,UInt64.le_iff_toNat_le] at after
            omega
          refine .inr ⟨(low,high,some (.ok middle)),?_,?_,?_⟩
          · simp [scan,middle,middleValid,before,after,nonempty]
          · exact ⟨ordered,bounded,middleValid,starts,stops⟩
          · change 0 < high-low+1
            omega
  have initial : Invariant map offset (0,map.entries.size,none) := by
    dsimp only [Invariant]
    obtain ⟨index,valid,start,stop⟩ := covered
    exact ⟨by omega,by omega,index,by omega,valid,valid,start,stop⟩
  have finished := loop_finished scan measure (Invariant map offset) (Finished map offset) step
    (0,map.entries.size,none) initial
  obtain ⟨index,found,contains⟩ := finished
  exact ⟨index,by rw [found],contains⟩
end DuplicatePrefix.GeneralRangeMapFind
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralRangeMapFind.find_success) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved general binary search axiom {dependency}"
