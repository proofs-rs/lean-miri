import duplicate_prefix.GeneralBorrowFreshGeometry
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
namespace DuplicatePrefix.GeneralBorrowFreshSharedGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem append_frame (input : GeneralBorrowFreshMetadataChildShared.Input) :
    (GeneralBorrowFreshMetadataChildShared.result input).locations.WellFormed ∧
      (GeneralBorrowFreshMetadataChildShared.result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location
      (GeneralBorrowFreshMetadataChildShared.index input) sharedState) input.well input.bounds
  have wellStage : (GeneralBorrowFreshMetadataChildShared.stage input).locations.WellFormed := modified.1
  have sizeStage : (GeneralBorrowFreshMetadataChildShared.stage input).locations.size = input.tree.locations.size :=
    congrArg Size.mk modified.2
  have frame := GeneralBorrowFreshGeometry.shape_frame (GeneralBorrowFreshMetadataChildShared.stage input)
    (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.shape input) wellStage
  exact ⟨frame.1,frame.2.trans sizeStage⟩

theorem reuse_frame (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) :
    (GeneralBorrowFreshMetadataChildSharedReuse.result input).locations.WellFormed ∧
      (GeneralBorrowFreshMetadataChildSharedReuse.result input).locations.size = input.tree.locations.size := by
  have modified := GeneralBorrowFreshRangeFrame.modifyRange_frame input.tree.locations (Size.ofBytes input.offset)
    (Size.ofBytes input.len) (fun _ location => GeneralBorrowFreshMaterialization.materialized location input.index sharedState)
    input.well input.bounds
  have wellStage : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).locations.WellFormed := modified.1
  have sizeStage : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).locations.size = input.tree.locations.size :=
    congrArg Size.mk modified.2
  have frame := GeneralBorrowFreshGeometry.shape_frame (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
    (GeneralBorrowFreshMetadataChildSharedReuse.result input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input) wellStage
  exact ⟨frame.1,frame.2.trans sizeStage⟩
end DuplicatePrefix.GeneralBorrowFreshSharedGeometry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedGeometry." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared geometry dependency {dependency}"
