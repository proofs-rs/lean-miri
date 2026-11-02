import duplicate_prefix.GeneralBorrowProtectedReadInvariant
import duplicate_prefix.GeneralBorrowFreshOwnership
namespace DuplicatePrefix.GeneralBorrowProtectedReadShape
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowFreshOwnership
open DuplicatePrefix.GeneralBorrowProtectedReadInvariant
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem state_factor (tree : NormalTreeState) (position : Nat) :
    (tree.stateAt position).map stateShape =
      match (tree.locationStates.map (Option.map stateShape))[position]? with
      | none => none
      | some (some shape) => some shape
      | some none => (tree.defaultStates.map stateShape)[position]? := by
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_map]
  cases tree.locationStates[position]? with
  | none => rfl
  | some row => cases row <;> rfl

private theorem state_transport (before after : NormalTreeState) (same : normalShape after = normalShape before)
    (position : Nat) (state : LocationState) (present : before.stateAt position = some state) :
    ∃ next, after.stateAt position = some next ∧ stateShape next = stateShape state := by
  have defaults : after.defaultStates.map stateShape = before.defaultStates.map stateShape :=
    congrArg (fun row => row.2.1) same
  have locations : after.locationStates.map (Option.map stateShape) = before.locationStates.map (Option.map stateShape) :=
    congrArg (fun row => row.2.2.1) same
  have lookup : (after.stateAt position).map stateShape = some (stateShape state) := by
    rw [state_factor,locations,defaults]
    rw [←state_factor,present]
    rfl
  cases actual : after.stateAt position with
  | none => rw [actual] at lookup; cases lookup
  | some next => rw [actual] at lookup; exact ⟨next,rfl,Option.some.inj lookup⟩


/-- The all-tag readable invariant ignores SIFA and exposure-cache values. -/
theorem normal (before after : NormalTreeState) (same : normalShape after = normalShape before)
    (initial : Data before) : Data after := by
  have locations : after.locationStates.size = before.locationStates.size := by
    have rows := congrArg (fun row => row.2.2.1) same
    simpa only [normalShape,Array.size_map] using congrArg Array.size rows
  have held : after.protectedNodes = before.protectedNodes := congrArg (fun row => row.2.2.2) same
  intro position valid
  obtain ⟨state,present,good⟩ := initial position (by omega)
  obtain ⟨next,stored,shape⟩ := state_transport before after same position state present
  refine ⟨next,stored,?_⟩
  rw [held]
  unfold Readable LocationState.possible
  change (next.accessed || !next.permission.isUnique) = true ∧ _
  unfold stateShape at shape
  simp only [Prod.mk.injEq] at shape
  rcases shape with ⟨permission,accessed⟩
  simpa only [Readable,LocationState.possible,permission,accessed] using good

/-- Actual ancestor-SIFA output retains readable profiles on the full map. -/
theorem tree (before after : BorrowTree) (protections : ProtectedTags) (same : treeShape after = treeShape before)
    (initial : Every (fun location => Data (source_normal_projection before location protections)) before.locations) :
    Every (fun location => Data (source_normal_projection after location protections)) after.locations := by
  have nodes := congrArg (fun row => row.2.1) same
  have rows := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) = before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  change after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) at nodes
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [normalShape,Array.size_map] using congrArg Array.size rows
  intro position valid
  have oldValid : position < before.locations.entries.size := by omega
  have row := congrArg (fun entries => entries[position]?) rows
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at row
  have pair := Prod.mk.inj (Option.some.inj row)
  exact normal _ _ (projection_shape before after _ _ protections nodes pair.2) (initial position oldValid)
end DuplicatePrefix.GeneralBorrowProtectedReadShape
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadShape.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read shape dependency {dependency}"
