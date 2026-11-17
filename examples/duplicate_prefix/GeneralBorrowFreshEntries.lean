import duplicate_prefix.GeneralBorrowLoop
import Miri.TreeBorrows.UniMap
namespace DuplicatePrefix.GeneralBorrowFreshEntries
open Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

private def accumulate {α β : Type} (select : α → Option β) (item : α) (out : Array β) : Id (ForInStep (Array β)) :=
  .yield (match select item with | none => out | some value => out.push value)

private theorem accumulate_exact {α β : Type} (items : List α) (select : α → Option β) (out : Array β) :
    forIn items out (accumulate select) = out ++ (items.filterMap select).toArray := by
  induction items generalizing out with
  | nil => simp [List.forIn_nil,pure]
  | cons item rest ih =>
    rw [List.forIn_cons]
    cases chosen : select item with
    | none => simp only [accumulate,chosen,bind,pure,List.filterMap_cons_none chosen]; exact ih out
    | some value =>
      simp only [accumulate,chosen,bind,pure,List.filterMap_cons_some chosen]
      rw [ih]
      exact List.push_append_toArray

def slot {α : Type} (data : Array (Option α)) (position : Nat) : Option (UniIndex × α) :=
  match UniIndex.ofNat? position, data[position]? with
  | some index, some (some value) => some (index,value)
  | _, _ => none

private def scan {α : Type} (data : Array (Option α)) (position : Nat) (out : Array (UniIndex × α)) :
    Id (ForInStep (Array (UniIndex × α))) :=
  match UniIndex.ofNat? position, data[position]? with
  | some index, some (some value) => .yield (out.push (index,value))
  | _, _ => .yield out

private theorem scan_accumulates {α : Type} (data : Array (Option α)) : scan data = accumulate (slot data) := by
  funext position out
  unfold scan accumulate slot
  cases UniIndex.ofNat? position <;> cases data[position]? with
  | none => rfl
  | some entry => cases entry <;> rfl

/-- A closed formula for the actual index-filtering loop. Indices beyond the
source u32 limit and absent values are filtered exactly as in UniValMap.entries. -/
theorem entries_formula {α : Type} (nodes : UniValMap α) :
    nodes.entries = ((List.range' 0 nodes.data.size).filterMap (slot nodes.data)).toArray := by
  unfold UniValMap.entries
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change forIn (List.range' 0 nodes.data.size) #[] (scan nodes.data) = _
  rw [scan_accumulates,accumulate_exact]
  simp

/-- Mapping stored data commutes with the real entries enumeration, preserving
all allocation-local indices. This is an enumeration law, not an access result. -/
theorem entries_map {α β : Type} (shape : α → β) (nodes : UniValMap α) :
    (⟨nodes.data.map (Option.map shape)⟩ : UniValMap β).entries =
      nodes.entries.map (fun row => (row.1,shape row.2)) := by
  have slots : slot (nodes.data.map (Option.map shape)) =
      fun position => (slot nodes.data position).map (fun row => (row.1,shape row.2)) := by
    funext position
    unfold slot
    simp only [Array.getElem?_map]
    cases UniIndex.ofNat? position <;> cases nodes.data[position]? with
    | none => rfl
    | some entry => cases entry <;> rfl
  rw [entries_formula,entries_formula]
  simp only [Array.size_map,slots,List.map_toArray,List.map_filterMap]

end DuplicatePrefix.GeneralBorrowFreshEntries
#print axioms DuplicatePrefix.GeneralBorrowFreshEntries.entries_map
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshEntries." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved indexed enumeration dependency {dependency}"
