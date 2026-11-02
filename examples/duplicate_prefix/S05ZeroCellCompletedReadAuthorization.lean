import duplicate_prefix.S05ZeroCellCompletedBorrowModel
import duplicate_prefix.S05CompletedAncestryReadQueries

/-! The generated eleven-node pre-copy row consumes completed-ancestry Read
authority at original/A. This is the current row, not the state after the
normal source Read or preceding callbacks. Runtime representation conditions
remain explicit in the production-visitor corollary. -/
namespace DuplicatePrefix.S05ZeroCellCompletedReadAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix GeneralBorrowExposedNonleafPrimaryPath
open S05ZeroCellCurrentCorrelation (raw held)
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxHeartbeats 1000000

def callbackRoot (position : Fin 2) : UniIndex := if position.val = 0 then ix 0 else ix 1

private theorem callback_slot (position : Fin 2) :
    raw.roots[position.val]? = some (callbackRoot position) := by
  rcases position with ⟨position,bound⟩
  have cases : position = 0 ∨ position = 1 := by omega
  rcases cases with rfl | rfl
  · exact S05ZeroCellCompletedBorrowModel.slots.1
  · exact S05ZeroCellCompletedBorrowModel.slots.2.1

private theorem callback_different (position : Fin 2) : callbackRoot position ≠ ix 3 := by
  rcases position with ⟨position,bound⟩
  have cases : position = 0 ∨ position = 1 := by omega
  rcases cases with rfl | rfl
  · change ix 0 ≠ ix 3
    decide
  · change ix 1 ≠ ix 3
    decide

/-- No source rights, chosen supporter, callback outcome or old Row are caller
premises. The selected B root supplies the actual tag4 cutoff. -/
theorem authorization (position : Fin 2) :
    Authorization raw S05ZeroCellCompletedBorrowModel.location held (callbackRoot position)
      position.val (some (tag 4)) .Read (Path raw (callbackRoot position)) := by
  simpa only [S05ZeroCellCompletedBorrowModel.selected_tag] using
    S05CompletedAncestryReadQueries.authorization raw S05ZeroCellCompletedBorrowModel.completion
      S05ZeroCellCompletedBorrowModel.location held S05ZeroCellCompletedBorrowModel.complete
      S05ZeroCellCompletedBorrowModel.depth S05ZeroCellCompletedBorrowModel.order position.val 2
      (callbackRoot position) (ix 3) (ix 10) (S05ZeroCellCurrentCorrelation.node raw ⟨3,by decide⟩)
      (callback_slot position) S05ZeroCellCompletedBorrowModel.slots.2.2
      (S05ZeroCellCompletedBorrowModel.node_present ⟨3,by decide⟩)
      (callback_different position) S05ZeroCellCompletedBorrowModel.source_path
      (fun _ _ found below => S05ZeroCellCompletedBorrowModel.local_rights found below)
      (fun _ _ found outside => S05ZeroCellCompletedBorrowModel.foreign_rights found outside)

/-- The existing production Read visitor consumes the concrete authorization.
The remaining premises describe graph/runtime representation and resources,
not success or future source permissions. Post-normal/prior-root transport is
a separate obligation; this theorem deliberately concerns the pre-copy row. -/
theorem access (position : Fin 2)
    (formed : GeneralBorrowStructuralHistoryState.GraphState raw)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent raw S05ZeroCellCompletedBorrowModel.location held)
    (short : raw.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile raw S05ZeroCellCompletedBorrowModel.location held)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible raw S05ZeroCellCompletedBorrowModel.location) :
    let result := raw.performWildcardAccessAt S05ZeroCellCompletedBorrowModel.location (callbackRoot position)
      (some (tag 4)) .Read held (position.val != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame S05ZeroCellCompletedBorrowModel.location result.location ∧
      GeneralBorrowExposureCardinality.LocationCoherent raw result.location held ∧
      GeneralBorrowLocationSifaConsistency.Profile raw result.location held ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible raw result.location ∧
      S05SemanticReadEffects.Effects raw S05ZeroCellCompletedBorrowModel.location result.location held := by
  simpa only [S05ZeroCellCompletedBorrowModel.selected_tag] using
    S05CompletedAncestryReadQueries.access raw S05ZeroCellCompletedBorrowModel.completion
      S05ZeroCellCompletedBorrowModel.location held S05ZeroCellCompletedBorrowModel.complete
      S05ZeroCellCompletedBorrowModel.depth S05ZeroCellCompletedBorrowModel.order position.val 2
      (callbackRoot position) (ix 3) (ix 10) (S05ZeroCellCurrentCorrelation.node raw ⟨3,by decide⟩)
      (callback_slot position) S05ZeroCellCompletedBorrowModel.slots.2.2
      (S05ZeroCellCompletedBorrowModel.node_present ⟨3,by decide⟩)
      (callback_different position) S05ZeroCellCompletedBorrowModel.source_path
      (fun _ _ found below => S05ZeroCellCompletedBorrowModel.local_rights found below)
      (fun _ _ found outside => S05ZeroCellCompletedBorrowModel.foreign_rights found outside)
      formed coherent short profile possible

end DuplicatePrefix.S05ZeroCellCompletedReadAuthorization

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCompletedReadAuthorization." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved completed Read consumer dependency {dependency}"
