import duplicate_prefix.GeneralRangeMapOrigins
import duplicate_prefix.GeneralRangeMapScanComplete
namespace DuplicatePrefix.GeneralRangeMapOriginScan
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapOrigins GeneralRangeMapScan GeneralRangeMapScanSafety
open DuplicatePrefix.GeneralRangeMapGeometry GeneralRangeMapInvariant GeneralRangeMapMerge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- All entries accumulated into the next candidate merge carry the same raw
value. Geometry-only preparation safety does not need this stronger invariant. -/
def EqualRun (map : DedupRangeMap α) (first current : Nat) : Prop :=
  ∀ position (valid : position < map.entries.size) (lower : first ≤ position) (upper : position ≤ current),
    map.entries[position].data = (map.entries[first]'(by omega)).data

private theorem singleton_run (map : DedupRangeMap α) (position : Nat) : EqualRun map position position := by
  intro index valid lower upper
  have same : index = position := by omega
  subst index
  rfl

/-- Pointwise source witnesses and the active equal-value run. Once the merge
budget is zero, no further merge needs the run property. -/
def OriginState (original : DedupRangeMap α) (state : State α) : Prop :=
  Refines original state.1 ∧
    (0 < state.2.2.1 → state.2.2.2.2.1 = false → EqualRun state.1 state.2.1 state.2.2.2.1)

/-- One iteration of the actual source-factored preparation scan preserves
pointwise origins. Successful operations are derived from well-formed geometry
and equal-run data; none is an input premise. -/
theorem step_preserves [DecidableEq α] (original : DedupRangeMap α)
    (offset finish capacity : UInt64) (first : Nat) (inside : finish.toNat ≤ capacity.toNat)
    (state : State α) (good : Good (fun _ => True) offset finish capacity first state)
    (origin : OriginState original state) :
    OriginState original (step finish () state).value := by
  rcases state with ⟨map,equal,count,index,done,failure⟩
  have data := good
  simp only [Good] at data
  rcases data with ⟨well,all,cap,failureEq,firstLE,equalLE,indexLE,firstValid,start,position⟩
  subst failure
  cases done with
  | true =>
    rw [idle map equal count index finish]
    exact origin
  | false =>
    rcases origin with ⟨refined,run⟩
    dsimp only at refined run
    simp only [Bool.false_eq_true,↓reduceIte] at position
    obtain ⟨current,startFinish⟩ := position
    have equalValid : equal < map.entries.size := by omega
    have insideMap : finish.toNat ≤ map.size.bytes.toNat := by rw [cap];exact inside
    have nextValid : map.entries[index].range.stop < finish → index+1 < map.entries.size :=
      GeneralRangeMapInvariant.next_valid map index current finish insideMap
    have alternatives :
        (count = 0 ∨ ∃ (before : map.entries[index].range.stop < finish) (eqValid : equal < map.entries.size),
          (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data) ∨
        (0 < count ∧ (finish ≤ map.entries[index].range.stop ∨
          ∃ before : map.entries[index].range.stop < finish,
            (map.entries[index+1]'(nextValid before)).data ≠ map.entries[equal].data)) := by
      by_cases zero : count = 0
      · exact .inl (.inl zero)
      · have positive : 0 < count := by omega
        by_cases complete : finish ≤ map.entries[index].range.stop
        · exact .inr ⟨positive,.inl complete⟩
        · have before : map.entries[index].range.stop < finish := by
            apply UInt64.lt_iff_toNat_lt.mpr
            simp only [UInt64.le_iff_toNat_le] at complete
            omega
          by_cases same : (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data
          · exact .inl (.inr ⟨before,equalValid,same⟩)
          · exact .inr ⟨positive,.inr ⟨before,same⟩⟩
    rcases alternatives with plain | ⟨positive,chosen⟩
    · rw [advance_no_merge map equal count index finish current nextValid plain]
      dsimp only [OriginState,ForInStep.value]
      refine ⟨refined,?_⟩
      intro positive active
      have previous := run positive rfl
      intro position valid lower upper
      rcases plain with zero | ⟨before,eqValid,same⟩
      · omega
      · by_cases earlier : position ≤ index
        · exact previous position valid lower earlier
        · have newest : position = index+1 := by omega
          subst position
          exact same
    · by_cases same : equal = index
      · subst equal
        rw [advance_merge_single map count index finish current positive nextValid chosen]
        dsimp only [OriginState,ForInStep.value]
        exact ⟨refined,fun _ _ => singleton_run map (index+1)⟩
      · have earlier : equal < index := by omega
        have sameData : ∀ position (atFirst : equal ≤ position) (beforeStop : position < index+1),
            (map.entries[position]'(by omega)).data = (map.entries[equal]'(by omega)).data := by
          intro position lower upper
          exact run positive rfl position (by omega) lower (by omega)
        have merged := merge_refines map equal (index+1) (by omega) (by omega) well sameData
        rw [advance_merge_many map equal count index finish current positive earlier nextValid chosen]
        dsimp only [OriginState,ForInStep.value]
        exact ⟨transitive original map _ refined merged,fun _ _ => singleton_run _ (equal+1)⟩


/-- The complete source preparation scan terminates while retaining pointwise
origins and its equal-data run. This strengthens the old geometry invariant in
a separate proof; the source scan and its comparison constraints are unchanged. -/
theorem finishes [DecidableEq α] (original : DedupRangeMap α)
    (offset finish capacity : UInt64) (first : Nat) (inside : finish.toNat ≤ capacity.toNat)
    (initial : State α) (good : Good (fun _ => True) offset finish capacity first initial)
    (owned : OriginState original initial) :
    let final := Lean.Loop.forIn (m := Id) {} initial (step finish)
    Good (fun _ => True) offset finish capacity first final ∧ OriginState original final ∧ final.2.2.2.2.1 = true := by
  apply GeneralRangeMapFind.loop_finished (step finish) GeneralRangeMapScanSafety.measure
    (fun state => Good (fun _ => True) offset finish capacity first state ∧ OriginState original state)
    (fun state => Good (fun _ => True) offset finish capacity first state ∧ OriginState original state ∧ state.2.2.2.2.1 = true)
    _ initial ⟨good,owned⟩
  intro state invariant
  have validState := invariant.1
  have origin := invariant.2
  have nextOrigin := step_preserves original offset finish capacity first inside state validState origin
  rcases state with ⟨map,equal,count,index,done,failure⟩
  have data := validState
  simp only [Good] at data
  rcases data with ⟨well,all,cap,failureEq,firstLE,equalLE,indexLE,firstValid,start,position⟩
  subst failure
  cases done with
  | true => exact .inl ⟨_,idle map equal count index finish,validState,origin,rfl⟩
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at position
    obtain ⟨current,startFinish⟩ := position
    have equalValid : equal < map.entries.size := by omega
    have insideMap : finish.toNat ≤ map.size.bytes.toNat := by rw [cap];exact inside
    have nextValid : map.entries[index].range.stop < finish → index+1 < map.entries.size :=
      next_valid map index current finish insideMap
    have alternatives :
        (count = 0 ∨ ∃ (before : map.entries[index].range.stop < finish) (eqValid : equal < map.entries.size),
          (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data) ∨
        (0 < count ∧ (finish ≤ map.entries[index].range.stop ∨
          ∃ before : map.entries[index].range.stop < finish,
            (map.entries[index+1]'(nextValid before)).data ≠ map.entries[equal].data)) := by
      by_cases zero : count = 0
      · exact .inl (.inl zero)
      · have positive : 0 < count := by omega
        by_cases complete : finish ≤ map.entries[index].range.stop
        · exact .inr ⟨positive,.inl complete⟩
        · have before : map.entries[index].range.stop < finish := by
            apply UInt64.lt_iff_toNat_lt.mpr
            simp only [UInt64.le_iff_toNat_le] at complete
            omega
          by_cases same : (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data
          · exact .inl (.inr ⟨before,equalValid,same⟩)
          · exact .inr ⟨positive,.inr ⟨before,same⟩⟩
    rcases alternatives with plain | ⟨positive,chosen⟩
    · let next : State α := (map,equal,count,index+1,decide (finish ≤ map.entries[index].range.stop),none)
      refine .inr ⟨next,advance_no_merge map equal count index finish current nextValid plain,?_,?_⟩
      · constructor
        · exact plain_good (fun _ : α => True) offset finish capacity first map equal count index current validState inside
            equal count firstLE (by omega)
        · have known := nextOrigin
          rw [advance_no_merge map equal count index finish current nextValid plain] at known
          exact known
      · by_cases complete : finish ≤ map.entries[index].range.stop <;> simp [GeneralRangeMapScanSafety.measure,next,complete] <;> omega
    · by_cases same : equal = index
      · subst equal
        let next : State α := (map,index+1,count-1,index+1,decide (finish ≤ map.entries[index].range.stop),none)
        refine .inr ⟨next,advance_merge_single map count index finish current positive nextValid chosen,?_,?_⟩
        · constructor
          · exact plain_good (fun _ : α => True) offset finish capacity first map index count index current validState inside
              (index+1) (count-1) (by omega) (by omega)
          · have known := nextOrigin
            rw [advance_merge_single map count index finish current positive nextValid chosen] at known
            exact known
        · by_cases complete : finish ≤ map.entries[index].range.stop <;> simp [GeneralRangeMapScanSafety.measure,next,complete] <;> omega
      · have earlier : equal < index := by omega
        let next : State α := (mergeMap map equal (index+1) (by omega) (by omega),equal+1,count+(index-equal),equal+1,
          decide (finish ≤ map.entries[index].range.stop),none)
        refine .inr ⟨next,advance_merge_many map equal count index finish current positive earlier nextValid chosen,?_,?_⟩
        · constructor
          · exact merged_good (fun _ : α => True) offset finish capacity first map equal count index current earlier validState inside
          · have known := nextOrigin
            rw [advance_merge_many map equal count index finish current positive earlier nextValid chosen] at known
            exact known
        · have resultSize : (mergeMap map equal (index+1) (by omega) (by omega)).entries.size =
              map.entries.size-(index-equal) := by rw [length];congr 1;omega
          by_cases complete : finish ≤ map.entries[index].range.stop <;>
            simp [GeneralRangeMapScanSafety.measure,next,complete,resultSize] <;> omega

end DuplicatePrefix.GeneralRangeMapOriginScan
#print axioms DuplicatePrefix.GeneralRangeMapOriginScan.step_preserves
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapOriginScan." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved preparation origin-scan dependency {dependency}"
