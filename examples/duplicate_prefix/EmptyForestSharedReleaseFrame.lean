import duplicate_prefix.EmptyForestSharedAppendNext

namespace DuplicatePrefix.EmptyForestSharedReleaseFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {tree : BorrowTree} {parentTag tag : BorTag}

/-- An existing unmaterialized reference survives real zero shared attachment and
Read-SIFA weakening, including when it is the selected parent. -/
theorem old_node (input : EmptyForestSharedAppend.Input tree parentTag tag)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node) :
    ∃ next, input.after.nodeAt query = some next ∧ next.isExposed = node.isExposed := by
  have stage : ∃ next, input.stage.nodeAt query = some next ∧ next.isExposed = node.isExposed := by
    by_cases same : query = input.parent
    · subst query
      have equal : input.parentNode = node := Option.some.inj (input.present.symm.trans present)
      refine ⟨updatedParent input.parentNode input.index,?_,?_⟩
      · simpa only [EmptyForestSharedAppend.Input.stage,BorrowTree.nodeAt] using
          (parent_lookup tree input.index input.parent input.parentNode (sharedNode tag input.parent) input.atEnd input.present)
      · simp only [updatedParent,equal]
    · have notNew : query ≠ input.index := by
        intro equal
        have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes query node present
        rw [equal,input.atEnd] at valid
        omega
      refine ⟨node,?_,rfl⟩
      simpa only [EmptyForestSharedAppend.Input.stage,BorrowTree.nodeAt] using
        ((other_lookup tree input.index input.parent query input.parentNode (sharedNode tag input.parent)
          input.atEnd input.present same notNew).trans present)
  obtain ⟨middle,lookup,flag⟩ := stage
  obtain ⟨next,found,_,_,_,_,exposed⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read query middle lookup
  exact ⟨next,found,exposed.trans flag⟩

/-- The old ROOT protector is genuinely releasable after another zero shared
constructor. Its absence of stored permissions is transported through the actual
SIFA loop, rather than postulated in the resulting tree. -/
theorem release (input : EmptyForestSharedAppend.Input tree parentTag tag)
    (oldTag : BorTag) (query : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag oldTag = some query) (present : tree.nodeAt query = some node)
    (unexposed : node.isExposed = false)
    (absent : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get query = none)
    (protections : ProtectedTags) :
    input.after.releaseProtector oldTag protections = ⟨input.after,.Released⟩ := by
  have taggedAfter : input.after.indexOfTag oldTag = some query := by
    unfold BorrowTree.indexOfTag
    rw [EmptyForestSharedAppendNext.mapping input]
    have different : tag ≠ oldTag := by
      intro equal
      subst oldTag
      simp only [BorrowTree.indexOfTag,UniKeyMap.get,
        GeneralBorrowTagMap.fresh_find tree.tagMapping tag input.fresh,Option.map_none] at tagged
      cases tagged
    exact (GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag oldTag different input.index tree.tagMapping.deassigned).trans tagged
  obtain ⟨next,lookup,exposed⟩ := old_node input query node present
  exact EmptyForestUnmaterializedRelease.release input.after oldTag query next taggedAfter lookup
    (exposed.trans unexposed) (EmptyForestSharedAppendNext.future_clean input query absent) protections

end DuplicatePrefix.EmptyForestSharedReleaseFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.EmptyForestSharedReleaseFrame." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty shared release frame {dependency}"
