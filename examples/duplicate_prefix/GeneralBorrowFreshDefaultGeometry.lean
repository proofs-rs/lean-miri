import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowFreshGeometry
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefault
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultReuse
namespace DuplicatePrefix.GeneralBorrowFreshDefaultGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshDefaultChild
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem append_frame (input : GeneralBorrowFreshMetadataChildDefault.Input) :
    (GeneralBorrowFreshMetadataChildDefault.result input).locations.WellFormed ∧
      (GeneralBorrowFreshMetadataChildDefault.result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location
      (GeneralBorrowFreshMetadataChildDefault.index input) inside) input.well input.bounds
  have wellStage : (GeneralBorrowFreshMetadataChildDefault.stage input).locations.WellFormed := modified.1
  have sizeStage : (GeneralBorrowFreshMetadataChildDefault.stage input).locations.size = input.tree.locations.size :=
    congrArg Size.mk modified.2
  have frame := GeneralBorrowFreshGeometry.shape_frame (GeneralBorrowFreshMetadataChildDefault.stage input)
    (GeneralBorrowFreshMetadataChildDefault.result input) (GeneralBorrowFreshMetadataChildDefault.shape input) wellStage
  exact ⟨frame.1,frame.2.trans sizeStage⟩

theorem reuse_frame (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input) :
    (GeneralBorrowFreshMetadataChildDefaultReuse.result input).locations.WellFormed ∧
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location input.index inside)
    input.well input.bounds
  have wellStage : (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).locations.WellFormed := modified.1
  have sizeStage : (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).locations.size = input.tree.locations.size :=
    congrArg Size.mk modified.2
  have frame := GeneralBorrowFreshGeometry.shape_frame (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
    (GeneralBorrowFreshMetadataChildDefaultReuse.result input) (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) wellStage
  exact ⟨frame.1,frame.2.trans sizeStage⟩
end DuplicatePrefix.GeneralBorrowFreshDefaultGeometry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshDefaultGeometry." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared geometry dependency {dependency}"
