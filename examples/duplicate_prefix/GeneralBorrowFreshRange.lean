import duplicate_prefix.GeneralRangeMapSafety
import duplicate_prefix.GeneralBorrowLoop
namespace DuplicatePrefix.GeneralBorrowFreshRange
open Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapState
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

elab "name_fresh_modify_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn.forIn)
      | throwError "no actual range modifier loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (←Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    let target ← goal.getType
    return [←goal.change (target.replace fun expr => if expr == body then some (mkFVar scan) else none)]

/-- The actual range modifier succeeds on every well-formed bounded partition.
The callback is an arbitrary pure Lean function; no iterator or update success
is an input assumption. -/
theorem modify_success {α : Type} [DecidableEq α] (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α) (well : map.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat) :
    (map.modifyRange offset len modify).outcome = .ok () := by
  let prepared := map.iterMutWithClone offset len id
  have preparedGood := GeneralRangeMapSafety.iter_mut_with_clone (fun _ : α => True)
    map offset len id well (fun _ _ => trivial) (fun _ _ => trivial) bounds
  unfold DedupRangeMap.modifyRange DedupRangeMap.modifyRangeWithClone
  simp only [Id.run,bind,pure,preparedGood.outcome,←Array.forIn_toList]
  name_fresh_modify_scan
  let property := fun state : Option (IterMutResult α) × DedupRangeMap α × Array (RangeMapSegment α) =>
    state.1 = none ∧ state.2.1.entries.size = prepared.state.entries.size
  have step : ∀ position ∈ prepared.positions.toList, ∀ state,
      property state → property (scan position state).value := by
    intro position member state good
    rcases state with ⟨returned,current,segments⟩
    rcases good with ⟨returnedEq,sizeEq⟩
    dsimp only at returnedEq sizeEq
    subst returned
    obtain ⟨cursor,cursorBound,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr member)
    have positionBound := (preparedGood.selected cursor cursorBound).choose
    rw [equal] at positionBound
    have valid : position < current.entries.size := by rw [sizeEq];exact positionBound
    let updated : RangeMapSegment α := {current.entries[position]'valid with
      data := modify (current.entries[position]'valid).range (current.entries[position]'valid).data}
    let next : DedupRangeMap α := ⟨current.entries.set position updated valid⟩
    have actual : scan position (none,current,segments) = .yield (none,next,segments.push updated) := by
      simp only [scan]
      unfold_range_update_source
      simp only [valid,↓reduceDIte,Except.pure,pure]
      rfl
    rw [actual]
    refine ⟨rfl,?_⟩
    simpa only [next,ForInStep.value,Array.size_set] using sizeEq
  have initial : property (none,prepared.state,#[]) := ⟨rfl,rfl⟩
  have maintained := GeneralBorrowLoop.list_invariant prepared.positions.toList scan property step _ initial
  rw [maintained.1]

end DuplicatePrefix.GeneralBorrowFreshRange
#print axioms DuplicatePrefix.GeneralBorrowFreshRange.modify_success
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshRange." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved range modification dependency {dependency}"
