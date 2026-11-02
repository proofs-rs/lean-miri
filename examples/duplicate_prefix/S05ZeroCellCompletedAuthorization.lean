import duplicate_prefix.S05ZeroCellCompletedBorrowModel
import duplicate_prefix.S05CompletedAncestryAuthorization

/-! The current eleven-node packet consumes the general completed-ancestry
Write rule at the two actual callback roots, original and A. This is adequacy
of the conservative residual masks on the pre-copy row; it does not identify
a postchildren mask or transport this row across the source Read. -/
namespace DuplicatePrefix.S05ZeroCellCompletedAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix GeneralBorrowExposedNonleafPrimaryPath
open S05ZeroCellCurrentCorrelation (raw held)
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Positions zero and one are the actual original/A callback roots; the
selected B source component is position two and is handled normally. -/
def callbackRoot (position : Fin 2) : UniIndex := if position.val = 0 then ix 0 else ix 1

private theorem callback_slot (position : Fin 2) :
    raw.roots[position.val]? = some (callbackRoot position) := by
  rcases position with ⟨position,bound⟩
  have cases : position = 0 ∨ position = 1 := by omega
  rcases cases with rfl | rfl
  · change raw.roots[0]? = some (ix 0)
    exact S05ZeroCellCompletedBorrowModel.slots.1
  · change raw.roots[1]? = some (ix 1)
    exact S05ZeroCellCompletedBorrowModel.slots.2.1

private theorem callback_different (position : Fin 2) : callbackRoot position ≠ ix 3 := by
  rcases position with ⟨position,bound⟩
  have cases : position = 0 ∨ position = 1 := by omega
  rcases cases with rfl | rfl
  · change ix 0 ≠ ix 3
    decide
  · change ix 1 ≠ ix 3
    decide

/-- At both actual non-selected roots, the generated tag13 source's current
completed ancestry and scalar transfer derive repaired authorization for every
legal mask and arbitrary entry. No callback outcome, supporter, raw authority
or representation clause is a caller premise. -/
theorem authorized (position : Fin 2) (query : UniIndex) (node : TreeNode)
    (present : raw.nodes.get query = some node)
    (path : Path raw (callbackRoot position) query)
    (removed : List UniIndex)
    (legal : Removal raw S05ZeroCellCompletedBorrowModel.location held (some (tag 4)) .Write removed)
    (entry : Option WildcardAccessRelatedness) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((S05ZeroCellCompletedBorrowModel.location.perms.get query).getD node.defaultLocationState)
      .Write (held.contains node.tag) entry
      (residualRelation raw S05ZeroCellCompletedBorrowModel.location held (callbackRoot position) query node
        (some (tag 4)) .Write position.val removed) := by
  have selectedPresent := S05ZeroCellCompletedBorrowModel.node_present ⟨3,by decide⟩
  have legal' : Removal raw S05ZeroCellCompletedBorrowModel.location held
      (some (S05ZeroCellCurrentCorrelation.node raw ⟨3,by decide⟩).tag) .Write removed := by
    simpa only [S05ZeroCellCompletedBorrowModel.selected_tag] using legal
  simpa only [S05ZeroCellCompletedBorrowModel.selected_tag] using
    S05CompletedAncestryAuthorization.authorized raw S05ZeroCellCompletedBorrowModel.completion
      S05ZeroCellCompletedBorrowModel.location held S05ZeroCellCompletedBorrowModel.complete
      S05ZeroCellCompletedBorrowModel.depth S05ZeroCellCompletedBorrowModel.order position.val 2
      (callbackRoot position) (ix 3) (ix 10) query node (S05ZeroCellCurrentCorrelation.node raw ⟨3,by decide⟩)
      (callback_slot position) S05ZeroCellCompletedBorrowModel.slots.2.2 selectedPresent
      (callback_different position) S05ZeroCellCompletedBorrowModel.source_path path present
      (fun _ _ found below => S05ZeroCellCompletedBorrowModel.local_rights found below)
      (fun _ _ found outside => S05ZeroCellCompletedBorrowModel.foreign_rights found outside)
      (S05ZeroCellCompletedBorrowModel.consistent present) removed legal' entry

end DuplicatePrefix.S05ZeroCellCompletedAuthorization
