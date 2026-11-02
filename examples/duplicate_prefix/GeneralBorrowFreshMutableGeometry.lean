import duplicate_prefix.GeneralBorrowFreshGeometry
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.GeneralBorrowFreshMutableGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshChild
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem append_frame (input : GeneralBorrowFreshMetadataChildMutable.Input) :
    (GeneralBorrowFreshMetadataChildMutable.result input).locations.WellFormed ∧
      (GeneralBorrowFreshMetadataChildMutable.result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location
      (GeneralBorrowFreshMetadataChildMutable.index input) inside) input.well input.bounds
  have wellStage : (GeneralBorrowFreshMetadataChildMutable.stage input).locations.WellFormed := modified.1
  have sizeStage : (GeneralBorrowFreshMetadataChildMutable.stage input).locations.size = input.tree.locations.size :=
    congrArg Size.mk modified.2
  have frame := GeneralBorrowFreshGeometry.shape_frame (GeneralBorrowFreshMetadataChildMutable.stage input)
    (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.shape input) wellStage
  exact ⟨frame.1,frame.2.trans sizeStage⟩

theorem reuse_frame (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) :
    (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations.WellFormed ∧
      (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location input.index inside)
    input.well input.bounds
  have wellStage : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations.WellFormed := modified.1
  have sizeStage : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations.size = input.tree.locations.size :=
    congrArg Size.mk modified.2
  have frame := GeneralBorrowFreshGeometry.shape_frame (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
    (GeneralBorrowFreshMetadataChildMutableReuse.result input) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) wellStage
  exact ⟨frame.1,frame.2.trans sizeStage⟩
end DuplicatePrefix.GeneralBorrowFreshMutableGeometry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMutableGeometry." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared geometry dependency {dependency}"
