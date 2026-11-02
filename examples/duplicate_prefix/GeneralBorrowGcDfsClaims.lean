import duplicate_prefix.GeneralBorrowGcDfsPendingFold

namespace DuplicatePrefix.GeneralBorrowGcDfsClaims
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcChildFold DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Existing kept representatives and unvisited source siblings all have real
current lookups with the active parent's exact parent index. -/
def Claims (tree : BorrowTree) (parent : UniIndex) (items : List UniIndex) : Prop :=
  ∀ index ∈ items, ∃ node, tree.nodes.get index = some node ∧ node.parent = some parent

private theorem removed_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

private theorem removal_success (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) : (source_remove_useless_node tree index).2 = .ok () := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]

private theorem remove_middle (kept rest : List UniIndex) (index : UniIndex)
    (distinct : (kept ++ index::rest).Nodup) : (kept ++ rest).Nodup ∧ index ∉ kept ++ rest := by
  obtain ⟨keptDistinct,remainingDistinct,apart⟩ := List.nodup_append.mp distinct
  obtain ⟨notRest,restDistinct⟩ := List.nodup_cons.mp remainingDistinct
  refine ⟨List.nodup_append.mpr ⟨keptDistinct,restDistinct,?_⟩,?_⟩
  · intro left member right inRest
    exact apart left member right (List.mem_cons_of_mem _ inRest)
  · intro member
    rcases List.mem_append.mp member with earlier | later
    · exact apart index earlier index (by simp) rfl
    · exact notRest later

private theorem insert_middle (kept rest : List UniIndex) (index : UniIndex)
    (distinct : (kept ++ rest).Nodup) (outside : index ∉ kept ++ rest) :
    (kept ++ index::rest).Nodup := by
  obtain ⟨keptDistinct,restDistinct,apart⟩ := List.nodup_append.mp distinct
  apply List.nodup_append.mpr
  refine ⟨keptDistinct,List.nodup_cons.mpr ⟨fun member => outside (List.mem_append_right _ member),restDistinct⟩,?_⟩
  intro left member right later same
  rcases List.mem_cons.mp later with equal | inRest
  · exact outside (same.trans equal ▸ List.mem_append_left _ member)
  · exact apart left member right inRest same

private theorem claims_remove (tree : BorrowTree) (parent index : UniIndex) (items : List UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (outside : index ∉ items) (claims : Claims tree parent items) :
    Claims (source_remove_useless_node tree index).1 parent items := by
  intro query member
  obtain ⟨value,found,edge⟩ := claims query member
  have different : query ≠ index := by intro same;exact outside (same ▸ member)
  exact ⟨value,(removed_other tree index query node present different).trans found,edge⟩

/-- One actual callback maintains all kept/unvisited parent claims and their
joint distinctness. A collapse replacement cannot equal any claim: its OLD
parent is the completed child, whereas claims point to the pending parent. -/
theorem step (original seed tree : BorrowTree) (processed : List UniIndex) (root parent index : UniIndex)
    (live : Array BorTag) (kept : Array UniIndex) (rest : List UniIndex) (originalNode : TreeNode)
    (originalPresent : original.nodes.get index = some originalNode) (originalEdge : originalNode.parent = some parent)
    (completed : index ∈ processed) (pendingParent : parent ∉ processed)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent tree)
    (distinct : (kept.toList ++ index::rest).Nodup) (claims : Claims tree parent (kept.toList ++ index::rest)) :
    ∃ after result, childScan seed root live parent index (none,tree,kept) = .yield (none,after,result) ∧
      GeneralBorrowGcDfsPendingFold.Data original processed parent after ∧
      (result.toList ++ rest).Nodup ∧ Claims after parent (result.toList ++ rest) := by
  have dataAfter : ∀ after result, childScan seed root live parent index (none,tree,kept) = .yield (none,after,result) →
      GeneralBorrowGcDfsPendingFold.Data original processed parent after := by
    intro after result actual
    have preserved := GeneralBorrowGcDfsPendingFold.step original seed processed root parent index live originalNode
      originalPresent originalEdge completed pendingParent (none,tree,kept) ⟨data,by simp⟩
    rw [actual] at preserved
    exact preserved.1
  obtain ⟨node,present,edge⟩ := claims index (List.mem_append_right _ (by simp))
  have stripped := remove_middle kept.toList rest index distinct
  have claimsStripped : Claims tree parent (kept.toList ++ rest) := by
    intro query member
    apply claims
    rcases List.mem_append.mp member with old | later
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ later)
  cases useless : gc_useless tree index live with
  | true =>
    have success := removal_success tree index node present
    have actual : childScan seed root live parent index (none,tree,kept) =
        .yield (none,(source_remove_useless_node tree index).1,kept) := by
      cases removed : source_remove_useless_node tree index with
      | mk after outcome =>
        have ok : outcome = .ok () := by simpa only [removed] using success
        simp only [childScan,useless,↓reduceIte,removed,ok,pure]
    exact ⟨_,kept,actual,dataAfter _ kept actual,stripped.1,claims_remove tree parent index _ node present stripped.2 claimsStripped⟩
  | false =>
    cases candidate : gc_replacement tree index live with
    | none =>
      have actual : childScan seed root live parent index (none,tree,kept) = .yield (none,tree,kept.push index) := by
        simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,pure]
      refine ⟨tree,kept.push index,actual,data,?_,?_⟩
      · simpa only [Array.toList_push,List.append_assoc,List.singleton_append] using distinct
      · simpa only [Array.toList_push,List.append_assoc,List.singleton_append] using claims
    | some replacement =>
      obtain ⟨before,replacementNode,lookup,member,replacementPresent⟩ := GeneralBorrowGcEligibilityFacts.replacement_present tree index replacement live candidate
      have same := Option.some.inj (present.symm.trans lookup)
      subst before
      obtain ⟨value,valuePresent,valueParent⟩ := data.repaired.children index completed node present replacement member
      have same := Option.some.inj (replacementPresent.symm.trans valuePresent)
      subst value
      have outside : replacement ∉ kept.toList ++ index::rest := by
        intro member
        obtain ⟨claimed,claimedPresent,claimedParent⟩ := claims replacement member
        have same := Option.some.inj (replacementPresent.symm.trans claimedPresent)
        subst claimed
        have same := Option.some.inj (valueParent.symm.trans claimedParent)
        exact pendingParent (same ▸ completed)
      have different : replacement ≠ index := by intro same;subst replacement;exact outside (List.mem_append_right _ (by simp))
      have afterPresent := (removed_other tree index replacement node present different).trans replacementPresent
      let after := {(source_remove_useless_node tree index).1 with nodes := (source_remove_useless_node tree index).1.nodes.insert replacement {replacementNode with parent := some parent}}
      have success := removal_success tree index node present
      have actual : childScan seed root live parent index (none,tree,kept) = .yield (none,after,kept.push replacement) := by
        cases removed : source_remove_useless_node tree index with
        | mk current outcome =>
          have ok : outcome = .ok () := by simpa only [removed] using success
          have retained : current.nodes.get replacement = some replacementNode := by simpa only [removed] using afterPresent
          simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,after,removed,ok,retained,pure]
      have outsideStripped : replacement ∉ kept.toList ++ rest := by
        intro member
        rcases List.mem_append.mp member with old | later
        · exact outside (List.mem_append_left _ old)
        · exact outside (List.mem_append_right _ (List.mem_cons_of_mem _ later))
      have retainedClaims := claims_remove tree parent index _ node present stripped.2 claimsStripped
      have finalClaims : Claims after parent (kept.toList ++ replacement::rest) := by
        intro query member
        by_cases same : query = replacement
        · subst query
          exact ⟨_,GeneralBorrowNodeUpdate.insert_existing_get_same _ replacement replacementNode _ afterPresent,rfl⟩
        · have oldMember : query ∈ kept.toList ++ rest := by
            rcases List.mem_append.mp member with old | later
            · exact List.mem_append_left _ old
            · exact List.mem_append_right _ ((List.mem_cons.mp later).resolve_left same)
          obtain ⟨value,lookup,edge⟩ := retainedClaims query oldMember
          exact ⟨value,(GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement query replacementNode _ afterPresent same).trans lookup,edge⟩
      refine ⟨after,kept.push replacement,actual,dataAfter _ _ actual,?_,?_⟩
      · simpa only [Array.toList_push,List.append_assoc,List.singleton_append] using insert_middle kept.toList rest replacement stripped.1 outsideStripped
      · simpa only [Array.toList_push,List.append_assoc,List.singleton_append] using finalClaims

/-- The exact actual child fold completes with distinct surviving representatives
and real parent edges, preserving pending metadata and repaired old parents.
No kept-array legality, callback success or fold success is assumed. -/
theorem fold (original seed tree : BorrowTree) (processed : List UniIndex) (root parent : UniIndex)
    (live : Array BorTag) (items : List UniIndex) (kept : Array UniIndex)
    (originalChildren : ∀ index ∈ items, ∃ node, original.nodes.get index = some node ∧ node.parent = some parent)
    (completed : ∀ index ∈ items, index ∈ processed) (pendingParent : parent ∉ processed)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent tree)
    (distinct : (kept.toList ++ items).Nodup) (claims : Claims tree parent (kept.toList ++ items)) :
    ∃ after result, forIn (m := Id) items (none,tree,kept) (childScan seed root live parent) = (none,after,result) ∧
      GeneralBorrowGcDfsPendingFold.Data original processed parent after ∧ result.toList.Nodup ∧ Claims after parent result.toList := by
  induction items generalizing tree kept with
  | nil => exact ⟨tree,kept,rfl,data,by simpa using distinct,by simpa using claims⟩
  | cons index rest ih =>
    obtain ⟨node,present,edge⟩ := originalChildren index (by simp)
    obtain ⟨middle,accumulated,actual,middleData,middleDistinct,middleClaims⟩ := step original seed tree processed root parent index live kept rest node present edge
      (completed index (by simp)) pendingParent data distinct claims
    obtain ⟨after,result,tail,finalData,finalDistinct,finalClaims⟩ := ih middle accumulated
      (fun child member => originalChildren child (List.mem_cons_of_mem _ member))
      (fun child member => completed child (List.mem_cons_of_mem _ member)) middleData middleDistinct middleClaims
    refine ⟨after,result,?_,finalData,finalDistinct,finalClaims⟩
    rw [List.forIn_cons,actual]
    simpa only [bind] using tail

end DuplicatePrefix.GeneralBorrowGcDfsClaims
