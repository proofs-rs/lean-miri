import duplicate_prefix.GeneralBorrowFreshFutureClean
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
namespace DuplicatePrefix.GeneralBorrowFreshSharedFutureClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshFutureClean
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem append (input : GeneralBorrowFreshMetadataChildShared.Input) (query : UniIndex)
    (different : query ≠ GeneralBorrowFreshMetadataChildShared.index input) (clean : Clean input.tree query) :
    Clean (GeneralBorrowFreshMetadataChildShared.result input) query := by
  have modified := GeneralBorrowFreshFutureClean.modified input.tree.locations (GeneralBorrowFreshMetadataChildShared.index input) query
    (Size.ofBytes input.offset) (Size.ofBytes input.len) sharedState different input.well input.bounds clean
  have stageClean : Clean (GeneralBorrowFreshMetadataChildShared.stage input) query := modified
  exact GeneralBorrowFreshFutureClean.shape_preserves (GeneralBorrowFreshMetadataChildShared.stage input)
    (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.shape input) query stageClean

theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (query : UniIndex)
    (different : query ≠ input.index) (clean : Clean input.tree query) :
    Clean (GeneralBorrowFreshMetadataChildSharedReuse.result input) query := by
  have modified := GeneralBorrowFreshFutureClean.modified input.tree.locations (input.index) query
    (Size.ofBytes input.offset) (Size.ofBytes input.len) sharedState different input.well input.bounds clean
  have stageClean : Clean (GeneralBorrowFreshMetadataChildSharedReuse.stage input) query := modified
  exact GeneralBorrowFreshFutureClean.shape_preserves (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
    (GeneralBorrowFreshMetadataChildSharedReuse.result input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input) query stageClean
end DuplicatePrefix.GeneralBorrowFreshSharedFutureClean
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedFutureClean." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared future clean dependency {dependency}"
