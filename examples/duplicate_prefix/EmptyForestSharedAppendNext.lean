import duplicate_prefix.EmptyForestSharedAppend

namespace DuplicatePrefix.EmptyForestSharedAppendNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshAnchor
open DuplicatePrefix.EmptyForestSharedAppend
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {tree : BorrowTree} {parentTag tag : BorTag}

theorem mapping (input : Input tree parentTag tag) : input.after.tagMapping = input.mapping :=
  GeneralBorrowFreshMetadata.mapping input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read)

theorem future_clean (input : Input tree parentTag tag) (query : UniIndex)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get query = none) :
    ∀ position (valid : position < input.after.locations.entries.size),
      input.after.locations.entries[position].data.perms.get query = none :=
  GeneralBorrowSifaExactReadFrame.sifa_exact input.stage input.parent query none
    (by intro state impossible;cases impossible) clean

theorem node_exists (input : Input tree parentTag tag) :
    ∃ node, input.after.nodeAt input.index = some node ∧ node.isExposed = false := by
  have present : input.stage.nodeAt input.index = some (sharedNode tag input.parent) := by
    simpa only [Input.stage,BorrowTree.nodeAt] using
      (GeneralBorrowFreshGraph.new_lookup tree input.index input.parent input.parentNode (sharedNode tag input.parent)
        input.atEnd input.present)
  obtain ⟨node,lookup,_,_,_,_,unexposed⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read input.index (sharedNode tag input.parent) present
  exact ⟨node,lookup,unexposed⟩

noncomputable def node (input : Input tree parentTag tag) := Classical.choose (node_exists input)
theorem present (input : Input tree parentTag tag) : input.after.nodeAt input.index = some (node input) :=
  (Classical.choose_spec (node_exists input)).1

theorem node_size (input : Input tree parentTag tag) : input.after.nodes.size = tree.nodes.size+1 := by
  have prior : (tree.nodes.insert input.index (sharedNode tag input.parent)).get input.parent = some input.parentNode :=
    (append_get_other tree.nodes input.index input.parent _ input.atEnd
      (parent_not_fresh tree.nodes input.index input.parent input.parentNode input.atEnd input.present)).trans input.present
  have stageSize : input.stage.nodes.size = tree.nodes.size+1 := by
    simp only [Input.stage,GeneralBorrowFreshGraph.attached,attachedNodes]
    rw [GeneralBorrowNodeUpdate.insert_existing_size _ input.parent input.parentNode _ prior,
      append_size tree.nodes input.index (sharedNode tag input.parent) input.atEnd]
  exact (GeneralBorrowFreshMetadata.node_size input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read)).trans stageSize

/-- Form the next genuine zero shared/FnEntry stage from prior pure data. The
new parent node, allocator alignment and depth are derived; only the next tag's
initial freshness, numeric room and vacant permission data are additional. -/
noncomputable def next (input : Input tree parentTag tag) (nextTag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag) (different : tag ≠ nextTag)
    (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩ = none) :
    Input input.after tag nextTag where
  parent := input.index
  parentNode := node input
  depth := input.afterDepth
  tagged := by
    rw [mapping input]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag input.fresh input.index tree.tagMapping.deassigned
  present := present input
  fresh := by
    rw [mapping input]
    intro row member
    rcases Array.mem_push.mp member with old | last
    · exact fresh row old
    · cases last;exact different
  noFree := by rw [mapping input];exact input.noFree
  aligned := by
    have sizes := node_size input
    rw [mapping input]
    simpa only [Input.mapping,Array.size_push,UniValMap.size,input.aligned] using sizes.symm
  fits := by rw [mapping input];simpa only [Input.mapping,Array.size_push] using room
  clean := by
    intro position valid
    have preserved := future_clean input ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩ clean position valid
    simpa only [mapping input,Input.mapping,Array.size_push] using preserved

end DuplicatePrefix.EmptyForestSharedAppendNext
