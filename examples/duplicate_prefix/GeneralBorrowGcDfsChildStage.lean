import duplicate_prefix.GeneralBorrowGcDfsStage
import duplicate_prefix.GeneralBorrowGcReplacementMember

namespace DuplicatePrefix.GeneralBorrowGcDfsChildStage
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcDfsStage
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Good (original : BorrowTree) (processed : List UniIndex) (state : ChildState) : Prop :=
  Stage original processed state.2.1 ∧
    (∀ index ∈ state.2.2.toList, index ∈ processed) ∧
    ∀ result, state.1 = some result → Stage original processed result.tree

/-- Every real child callback mutates only the completed region. A collapsed
replacement belongs to that region because it is a current child of a completed
node; unprocessed original metadata stay untouched even during stale-edge phases. -/
theorem step (original seed : BorrowTree) (processed : List UniIndex)
    (root parent child : UniIndex) (live : Array BorTag) (member : child ∈ processed)
    (state : ChildState) (good : Good original processed state) :
    Good original processed (childScan seed root live parent child state).value := by
  rcases state with ⟨returned,current,kept⟩
  rcases good with ⟨stage,all,_⟩
  simp only [childScan,pure]
  split
  · have next := GeneralBorrowGcDfsStage.remove original current processed child member stage
    split <;> exact ⟨next,all,by intro result same;cases same <;> exact next⟩
  · split
    · refine ⟨stage,?_,?_⟩
      · intro index present
        rcases (Array.mem_push.mp (by simpa using present)) with old | same
        · exact all index (by simpa using old)
        · simpa only [same] using member
      · simp
    · rename_i replacement found
      obtain ⟨node,present,childMember⟩ := GeneralBorrowGcReplacementMember.member current child replacement live found
      have completed : replacement ∈ processed := stage.closed child member node present replacement childMember
      have next := GeneralBorrowGcDfsStage.remove original current processed child member stage
      split
      · exact ⟨next,all,by intro result same;cases same;exact next⟩
      · split
        · rename_i replacementNode replacementPresent
          have changed := GeneralBorrowGcDfsStage.reparent original (source_remove_useless_node current child).1
            processed replacement parent completed replacementNode replacementPresent next
          refine ⟨changed,?_,?_⟩
          · intro index present
            rcases (Array.mem_push.mp (by simpa using present)) with old | same
            · exact all index (by simpa using old)
            · simpa only [same] using completed
          · simp
        · exact ⟨next,all,by intro result same;cases same;exact next⟩

/-- Exact child-order folding preserves the staged completed/unprocessed split
and keeps only completed representatives. This does not assume or assert that
the callback avoided every error branch. -/
theorem fold (original seed : BorrowTree) (processed items : List UniIndex)
    (root parent : UniIndex) (live : Array BorTag)
    (members : ∀ child ∈ items, child ∈ processed) (state : ChildState)
    (good : Good original processed state) :
    Good original processed (forIn (m := Id) items state (childScan seed root live parent)) := by
  apply GeneralBorrowLoop.list_invariant items (childScan seed root live parent) (Good original processed)
  · intro child member current valid
    exact step original seed processed root parent child live (members child member) current valid
  · exact good
end DuplicatePrefix.GeneralBorrowGcDfsChildStage
