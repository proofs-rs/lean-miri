import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.GeneralBorrowExposeReadFold
namespace DuplicatePrefix.GeneralBorrowExposureMapFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
open Lean Elab Term in
elab "source_location_update" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.updateEveryLocation" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected pinned source location updater"

/-- The real generic location-update loop cannot edit the tag map, including
its range/cache error branches. -/
theorem locations (tree : BorrowTree) (update : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit) :
    (source_location_update tree update).tree.tagMapping = tree.tagMapping := by
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  name_release_exposure_scan
  let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    state.2.tagMapping = tree.tagMapping ∧ ∀ returned,state.1 = some returned → returned.tree.tagMapping = tree.tagMapping
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

/-- Actual exposeTag preserves allocator tag mapping on every outcome. -/
theorem expose (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) :
    (tree.exposeTag protections tag).tree.tagMapping = tree.tagMapping := by
  unfold BorrowTree.exposeTag
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
      · exact locations _ _

/-- Any actual exposure fold retains the exact map, even on early errors. -/
theorem run (requests : List Request) (tree : BorrowTree) (protections : ProtectedTags) :
    (GeneralBorrowExposeReadFold.run protections requests tree).tree.tagMapping = tree.tagMapping := by
  induction requests generalizing tree with
  | nil => rfl
  | cons request rest ih =>
    change (match (tree.exposeTag protections request.tag).outcome with
      | .error _ => tree.exposeTag protections request.tag
      | .ok () => GeneralBorrowExposeReadFold.run protections rest (tree.exposeTag protections request.tag).tree).tree.tagMapping = _
    cases outcome : (tree.exposeTag protections request.tag).outcome with
    | error error => exact expose tree protections request.tag
    | ok returned => cases returned;exact (ih _).trans (expose tree protections request.tag)
end DuplicatePrefix.GeneralBorrowExposureMapFrame
