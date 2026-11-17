import duplicate_prefix.GeneralBorrowLocationUpdateFrame
import duplicate_prefix.GeneralBorrowFreshReleaseLoop
namespace DuplicatePrefix.GeneralBorrowStructuralReleaseGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposureMapFrame DuplicatePrefix.GeneralBorrowExposureRelease
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem setAtPos_geometry (map : DedupRangeMap LocationTree) (position : Nat) (location : LocationTree)
    (well : map.WellFormed) :
    (map.setAtPos position location).state.WellFormed ∧ (map.setAtPos position location).state.size = map.size := by
  by_cases valid : position < map.entries.size
  · rw [setAtPos_exact map position valid]
    exact ⟨replaced_wellFormed map position valid location well,replaced_size map position valid location⟩
  · unfold DedupRangeMap.setAtPos
    unfold_range_update_source
    simp only [valid,↓reduceDIte,Id.run,pure]
    exact ⟨well,True.intro⟩

def Geometry (original current : BorrowTree) : Prop := current.locations.WellFormed ∧ current.locations.size = original.locations.size

/-- Generic source cache-location updater preserves partition geometry even
when a callback or map operation returns an error after an updated prefix. -/
theorem update (tree : BorrowTree) (callback : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit)
    (well : tree.locations.WellFormed) : Geometry tree (source_location_update tree callback).tree := by
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  name_release_exposure_scan
  let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    Geometry tree state.2 ∧ ∀ returned,state.1 = some returned → Geometry tree returned.tree
  have step : ∀ position member state,property state → property (scan position member state).value := by
    intro position member state good
    rcases state with ⟨returned,current⟩
    dsimp only [property] at good ⊢
    have mutationGood : ∀ location,Geometry tree {current with locations := (current.locations.setAtPos position location).state} := by
      intro location
      have changed := setAtPos_geometry current.locations position location good.1.1
      exact ⟨changed.1,changed.2.trans good.1.2⟩
    simp only [scan]
    repeat' first
      | split
      | exact ⟨good.1,fun result same => by cases same;exact good.1⟩
      | exact ⟨good.1,by simp⟩
      | exact ⟨mutationGood _,fun result same => by cases same;exact mutationGood _⟩
      | exact ⟨mutationGood _,by simp⟩
  have initial : property (none,tree) := ⟨⟨well,rfl⟩,by simp⟩
  have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant' _ scan property step _ initial
  split
  · exact final.2 _ (by assumption)
  · exact final.1

/-- Protector-release exposure updates preserve geometry on every outcome,
including absent tags/nodes and partially completed failing cache walks. -/
theorem exposure (tree : BorrowTree) (tag : BorTag) (well : tree.locations.WellFormed) :
    Geometry tree (tree.updateExposureForProtectorRelease tag).tree := by
  unfold BorrowTree.updateExposureForProtectorRelease
  cases tagged : tree.indexOfTag tag with
  | none => exact ⟨well,rfl⟩
  | some index =>
    simp only [Id.run,pure]
    cases present : tree.nodeAt index with
    | none => exact ⟨well,rfl⟩
    | some node =>
      dsimp only
      split
      · exact ⟨well,rfl⟩
      · exact update tree _ well

/-- Implicit protector-end Read/Write and exposure update preserve the real
partition's well-formedness and capacity on all outcomes. Errors may retain
updated values, but cannot edit range geometry. No bounds, ownership, tag
presence, protector activity, cache certificate or success premise is needed. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (well : tree.locations.WellFormed) :
    let result := tree.releaseProtector tag protections
    result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  unfold BorrowTree.releaseProtector
  cases tagged : tree.indexOfTag tag with
  | none => exact ⟨well,rfl⟩
  | some source =>
    simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_fresh_release_scan
    let property := fun state : Option BorrowTree.ProtectorReleaseResult × BorrowTree =>
      Geometry tree state.2 ∧ ∀ returned,state.1 = some returned → Geometry tree returned.tree
    have step : ∀ position ∈ List.range' 0 tree.locations.entries.size, ∀ state,
        property state → property (scan position state).value := by
      intro position member state good
      rcases state with ⟨returned,current⟩
      dsimp only [property] at good ⊢
      have mutationGood : ∀ location,Geometry tree {current with locations := (current.locations.setAtPos position location).state} := by
        intro location
        have changed := setAtPos_geometry current.locations position location good.1.1
        exact ⟨changed.1,changed.2.trans good.1.2⟩
      simp only [scan]
      repeat' first
        | split
        | exact ⟨good.1,fun result same => by cases same;exact good.1⟩
        | exact ⟨good.1,by simp⟩
        | exact ⟨mutationGood _,fun result same => by cases same;exact mutationGood _⟩
        | exact ⟨mutationGood _,by simp⟩
    have initial : property (none,tree) := ⟨⟨well,rfl⟩,by simp⟩
    have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step _ initial
    split
    · exact final.2 _ (by assumption)
    · have finish : ∀ current : BorrowTree,Geometry tree current →
          let changed := current.updateExposureForProtectorRelease tag
          Geometry tree (match changed.outcome with
            | .error error => (⟨changed.tree,.ExposureUpdateFailure error⟩ : BorrowTree.ProtectorReleaseResult)
            | .ok () => ⟨changed.tree,.Released⟩).tree := by
        intro current good
        have changed := exposure current tag good.1
        dsimp only
        split <;> exact ⟨changed.1,changed.2.trans good.2⟩
      exact finish _ final.1
end DuplicatePrefix.GeneralBorrowStructuralReleaseGeometry
