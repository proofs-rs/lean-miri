import duplicate_prefix.GeneralBorrowLocationUpdateProperty
namespace DuplicatePrefix.GeneralBorrowLocationUpdateFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual generic location-update loop retains all node metadata on every
outcome, including errors. -/
theorem nodes (tree : BorrowTree) (update : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit) :
    (source_location_update tree update).tree.nodes = tree.nodes := by
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  name_release_exposure_scan
  let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    state.2.nodes = tree.nodes ∧ ∀ returned,state.1 = some returned → returned.tree.nodes = tree.nodes
  have step : ∀ position member state,property state → property (scan position member state).value := by
    intro position member state good
    rcases state with ⟨returned,current⟩
    dsimp only [property] at good ⊢
    simp only [scan]
    repeat' first | split | exact ⟨good.1,fun result same => by cases same;exact good.1⟩ | exact ⟨good.1,by simp⟩
  have initial : property (none,tree) := ⟨rfl,by simp⟩
  have final := GeneralBorrowLoop.list_invariant' _ scan property step _ initial
  split
  · exact final.2 _ (by assumption)
  · exact final.1

end DuplicatePrefix.GeneralBorrowLocationUpdateFrame
