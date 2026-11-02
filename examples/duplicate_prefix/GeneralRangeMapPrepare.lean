import duplicate_prefix.GeneralRangeMapScan
namespace DuplicatePrefix.GeneralRangeMapPrepare
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapScan
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def finishPrepared (first : Nat) (finish : UInt64) (cloneData : α → α) (state : State α) : IterMutResult α := Id.run do
  match state.2.2.2.2.2 with
  | some error => return {state := state.1,positions := #[],segments := #[],outcome := .error error}
  | none =>
    let lastIndex := state.2.2.2.1-1
    match range_split_index state.1.entries lastIndex finish cloneData with
    | .error error => return {state := state.1,positions := #[],segments := #[],outcome := .error error}
    | .ok (entries,_) =>
      let current := {state.1 with entries}
      let selectedStop := lastIndex+1
      match range_selected_slice current.entries first selectedStop with
      | .error error => return {state := current,positions := #[],segments := #[],outcome := .error error}
      | .ok segments =>
        let positions := (List.range (selectedStop-first)).toArray.map (·+first)
        return {state := current,positions,segments,outcome := .ok ()}

theorem actual_prepared [DecidableEq α] (map start : DedupRangeMap α) (offset len : Size)
    (finish : UInt64) (cloneData : α → α) (first : Nat) (didSplit : Bool)
    (nonempty : len.bytes ≠ 0)
    (search : range_find_offset map offset.bytes = .ok first)
    (split : range_split_index map.entries first offset.bytes cloneData = .ok (start.entries,didSplit))
    (calculated : range_checked_end offset.bytes len.bytes = .ok finish) :
    map.iterMutWithClone offset len cloneData =
      finishPrepared (if didSplit then first+1 else first) finish cloneData
        (Lean.Loop.forIn (m := Id) {} (start,(if didSplit then first+1 else first),3,(if didSplit then first+1 else first),false,none)
          (GeneralRangeMapScan.step (α := α) finish)) := by
  unfold DedupRangeMap.iterMutWithClone
  simp only [nonempty,beq_iff_eq,↓reduceIte]
  rw [search]
  simp only [bind,pure,Id.instMonad]
  rw [split]
  cases didSplit
  all_goals
    simp only [Bool.false_eq_true,↓reduceIte]
    rw [calculated]
    simp only [ForIn.forIn]
    name_range_scan
    have scanEq : scan = GeneralRangeMapScan.step (α := α) finish := by
      funext loopUnit state
      rcases state with ⟨current,equalSince,count,index,done,failure⟩
      unfold GeneralRangeMapScan.step
      rfl
    rw [scanEq]
    unfold finishPrepared
    rfl
end DuplicatePrefix.GeneralRangeMapPrepare
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralRangeMapPrepare.actual_prepared) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual range prepare source fold {dependency}"
