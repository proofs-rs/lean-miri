import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowStructuralReleaseGeometryFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposureMapFrame DuplicatePrefix.GeneralBorrowExposureRelease
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
def Frame (original current : BorrowTree) : Prop := current = {original with locations := current.locations}

/-- All outcomes of the generic source updater change only locations. -/
theorem update (tree : BorrowTree) (callback : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit)
    : Frame tree (source_location_update tree callback).tree := by
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  name_release_exposure_scan
  let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    Frame tree state.2 ∧ ∀ returned,state.1 = some returned → Frame tree returned.tree
  have step : ∀ position member state,property state → property (scan position member state).value := by
    intro position member state good
    rcases state with ⟨returned,current⟩
    dsimp only [property] at good ⊢
    have mutationGood : ∀ location,Frame tree {current with locations := (current.locations.setAtPos position location).state} := by
      intro location
      have original : current = {tree with locations := current.locations} := good.1
      dsimp only [Frame]
      rw [original]
    simp only [scan]
    repeat' first
      | split
      | exact ⟨good.1,fun result same => by cases same;exact good.1⟩
      | exact ⟨good.1,by simp⟩
      | exact ⟨mutationGood _,fun result same => by cases same;exact mutationGood _⟩
      | exact ⟨mutationGood _,by simp⟩
  have initial : property (none,tree) := ⟨rfl,by simp⟩
  have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant' _ scan property step _ initial
  split
  · exact final.2 _ (by assumption)
  · exact final.1

/-- Protector exposure release changes only locations, including failure prefixes. -/
theorem exposure (tree : BorrowTree) (tag : BorTag) :
    Frame tree (tree.updateExposureForProtectorRelease tag).tree := by
  unfold BorrowTree.updateExposureForProtectorRelease
  cases tagged : tree.indexOfTag tag with
  | none => exact rfl
  | some index =>
    simp only [Id.run,pure]
    cases present : tree.nodeAt index with
    | none => exact rfl
    | some node =>
      dsimp only
      split
      · exact rfl
      · exact update tree _

/-- Real protector release changes only locations on every outcome. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    :
    let result := tree.releaseProtector tag protections
    result.tree = {tree with locations := result.tree.locations} := by
  unfold BorrowTree.releaseProtector
  cases tagged : tree.indexOfTag tag with
  | none => exact rfl
  | some source =>
    simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_fresh_release_scan
    let property := fun state : Option BorrowTree.ProtectorReleaseResult × BorrowTree =>
      Frame tree state.2 ∧ ∀ returned,state.1 = some returned → Frame tree returned.tree
    have step : ∀ position ∈ List.range' 0 tree.locations.entries.size, ∀ state,
        property state → property (scan position state).value := by
      intro position member state good
      rcases state with ⟨returned,current⟩
      dsimp only [property] at good ⊢
      have mutationGood : ∀ location,Frame tree {current with locations := (current.locations.setAtPos position location).state} := by
        intro location
        have original : current = {tree with locations := current.locations} := good.1
        dsimp only [Frame]
        rw [original]
      simp only [scan]
      repeat' first
        | split
        | exact ⟨good.1,fun result same => by cases same;exact good.1⟩
        | exact ⟨good.1,by simp⟩
        | exact ⟨mutationGood _,fun result same => by cases same;exact mutationGood _⟩
        | exact ⟨mutationGood _,by simp⟩
    have initial : property (none,tree) := ⟨rfl,by simp⟩
    have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step _ initial
    split
    · exact final.2 _ (by assumption)
    · have finish : ∀ current : BorrowTree,Frame tree current →
          let changed := current.updateExposureForProtectorRelease tag
          Frame tree (match changed.outcome with
            | .error error => (⟨changed.tree,.ExposureUpdateFailure error⟩ : BorrowTree.ProtectorReleaseResult)
            | .ok () => ⟨changed.tree,.Released⟩).tree := by
        intro current good
        have changed := exposure current tag
        dsimp only
        have joined : Frame tree (current.updateExposureForProtectorRelease tag).tree := by
          unfold Frame
          calc
            (current.updateExposureForProtectorRelease tag).tree = {current with locations := (current.updateExposureForProtectorRelease tag).tree.locations} := changed
            _ = _ := by rw [show current = {tree with locations := current.locations} from good]
        split <;> exact joined
      exact finish _ final.1
end DuplicatePrefix.GeneralBorrowStructuralReleaseGeometryFrame
