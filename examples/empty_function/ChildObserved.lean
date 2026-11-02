import empty_function.ChildSuccess

namespace EmptyFunction.ChildObserved
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The actual allocator distinguishes insertion from duplicate replacement. -/
theorem fresh_of_insert (mapping : UniKeyMap BorTag) (tag : BorTag)
    (after : UniKeyMap BorTag) (index : UniIndex)
    (inserted : mapping.insert tag = .Inserted after index) : mapping.get tag = none := by
  cases found : mapping.get tag with
  | none => rfl
  | some old =>
    cases available : mapping.deassigned.back? with
    | some free => simp [UniKeyMap.insert,available,found] at inserted
    | none =>
      cases generated : UniIndex.ofNat? mapping.mapping.size <;>
        simp [UniKeyMap.insert,available,generated,found] at inserted

/-- Every successful zero child has taken the real successful allocator branch;
its duplicate/exhaustion errors are retained by the source, not assumed absent. -/
theorem inserted_of_success (tree : BorrowTree) (tag : BorTag) (parent : ProvenanceExtra)
    (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset parent tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) :
    ∃ mapping index, tree.tagMapping.insert tag = .Inserted mapping index := by
  cases allocated : tree.tagMapping.insert tag with
  | Inserted mapping index => exact ⟨mapping,index,rfl⟩
  | DuplicateKeyAfterReplacement mapping index => simp [BorrowTree.newChild,allocated] at created
  | Error mapping error => simp [BorrowTree.newChild,allocated] at created

 theorem concrete_parent_of_success (tree : BorrowTree) (tag parentTag : BorTag)
    (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset (.concrete parentTag) tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) :
    ∃ parent, tree.tagMapping.get parentTag = some parent := by
  obtain ⟨mapping,index,inserted⟩ := inserted_of_success tree tag (.concrete parentTag) offset initial after created
  cases parent : tree.tagMapping.get parentTag with
  | some index => exact ⟨index,rfl⟩
  | none => simp [BorrowTree.newChild,inserted,parent] at created

/-- A successful concrete constructor supplies all freshness/parent evidence
needed for release. Only raw current-tree formation remains a precondition. -/
theorem concrete (tree : BorrowTree) (currentTag tag parentTag : BorTag)
    (formed : TreeRuntimeInput.TreeFormed tree currentTag)
    (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset (.concrete parentTag) tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) (protections : ProtectedTags) :
    after.releaseProtector tag protections = ⟨after,.Released⟩ ∧ Preservation.OldNodeRights tree after := by
  obtain ⟨mapping,index,inserted⟩ := inserted_of_success tree tag (.concrete parentTag) offset initial after created
  obtain ⟨parent,tagged⟩ := concrete_parent_of_success tree tag parentTag offset initial after created
  exact ChildSuccess.concrete tree currentTag tag formed
    (fresh_of_insert tree.tagMapping tag mapping index inserted) parentTag parent tagged offset initial after created protections

 theorem wildcard (tree : BorrowTree) (currentTag tag : BorTag)
    (formed : TreeRuntimeInput.TreeFormed tree currentTag)
    (offset : Size) (initial : LocationState) (after : BorrowTree)
    (created : tree.newChild offset .wildcard tag (DataStructures.DedupRangeMap.new Size.ZERO initial)
      (.ReservedFrz false) true = ⟨after,.ok ()⟩) (protections : ProtectedTags) :
    after.releaseProtector tag protections = ⟨after,.Released⟩ ∧ Preservation.OldNodeRights tree after := by
  obtain ⟨mapping,index,inserted⟩ := inserted_of_success tree tag .wildcard offset initial after created
  exact ChildSuccess.wildcard tree currentTag tag formed
    (fresh_of_insert tree.tagMapping tag mapping index inserted) offset initial after created protections

end EmptyFunction.ChildObserved
