import duplicate_prefix.GeneralBorrowParentTagOperations
import duplicate_prefix.GeneralBorrowLocationUpdateFrame
import duplicate_prefix.GeneralBorrowFreshReleaseLoop
namespace DuplicatePrefix.GeneralBorrowParentTagRelease
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureRelease GeneralBorrowExposureMapFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The actual release cache updater never edits nodes, including errors. -/
theorem exposure_nodes (tree : BorrowTree) (tag : BorTag) :
    (tree.updateExposureForProtectorRelease tag).tree.nodes = tree.nodes := by
  unfold BorrowTree.updateExposureForProtectorRelease
  cases tagged : tree.indexOfTag tag with
  | none => rfl
  | some index =>
    simp only [Id.run,pure]
    cases present : tree.nodeAt index with
    | none => rfl
    | some node =>
      dsimp only
      split
      · rfl
      · exact GeneralBorrowLocationUpdateFrame.nodes tree _

/-- Full actual implicit protector-end access and cache update retain nodes
on EVERY outcome, without ownership/activity or successful-release assumptions. -/
theorem release_nodes (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) :
    (tree.releaseProtector tag protections).tree.nodes = tree.nodes := by
  unfold BorrowTree.releaseProtector
  cases tagged : tree.indexOfTag tag with
  | none => rfl
  | some source =>
    simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_fresh_release_scan
    let property := fun state : Option BorrowTree.ProtectorReleaseResult × BorrowTree =>
      state.2.nodes = tree.nodes ∧ ∀ returned,state.1 = some returned → returned.tree.nodes = tree.nodes
    have step : ∀ position ∈ List.range' 0 tree.locations.entries.size, ∀ state,
        property state → property (scan position state).value := by
      intro position member state good
      rcases state with ⟨returned,current⟩
      dsimp only [property] at good ⊢
      simp only [scan]
      repeat' first
        | split
        | exact ⟨good.1,fun result same => by cases same;exact good.1⟩
        | exact ⟨good.1,by simp⟩
    have initial : property (none,tree) := ⟨rfl,by simp⟩
    have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
    split
    · exact final.2 _ (by assumption)
    · have finish : ∀ current : BorrowTree,current.nodes = tree.nodes →
          let changed := current.updateExposureForProtectorRelease tag
          (match changed.outcome with
            | .error error => (⟨changed.tree,.ExposureUpdateFailure error⟩ : BorrowTree.ProtectorReleaseResult)
            | .ok () => ⟨changed.tree,.Released⟩).tree.nodes = tree.nodes := by
        intro current good
        have changed := (exposure_nodes current tag).trans good
        dsimp only
        split <;> exact changed
      exact finish _ final.1

theorem release_order (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (order : ParentTagOrder tree) : ParentTagOrder (tree.releaseProtector tag protections).tree :=
  GeneralBorrowParentTagInvariant.nodes_frame tree _ (release_nodes tree protections tag) order
end DuplicatePrefix.GeneralBorrowParentTagRelease
