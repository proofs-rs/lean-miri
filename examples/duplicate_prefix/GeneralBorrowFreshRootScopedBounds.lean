import duplicate_prefix.GeneralBorrowFreshRootScopedRow
import duplicate_prefix.GeneralBorrowSharedCallbacksAttach
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedBounds
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshRootSupportCutoff GeneralBorrowFreshNode GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

theorem attach_metadata (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) :
    ∃ next,(attachedNodes tree.nodes index parent parentNode newNode).get query = some next ∧
      next.tag = node.tag ∧ next.isExposed = node.isExposed := by
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;contradiction
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  have queryDifferent : query ≠ index := by intro same;rw [same,vacant] at present;contradiction
  by_cases same : query = parent
  · subst query
    have equal := Option.some.inj (present.symm.trans parentPresent)
    subst node
    exact ⟨{parentNode with children := parentNode.children.push index},
      insert_existing_get_same _ parent parentNode _ parentAfter,rfl,rfl⟩
  · refine ⟨node,?_,rfl,rfl⟩
    unfold attachedNodes
    rw [GeneralBorrowFreshLocation.get_other _ parent query _ same,
      GeneralBorrowFreshLocation.get_other _ index query _ queryDifferent,present]

theorem support_attach (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (maximum : BorTag) (support : UniIndex → Prop)
    (present : ∀ query,support query → ∃ node,tree.nodes.get query = some node)
    (bound : SupportBound tree maximum support) :
    SupportBound {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} maximum support := by
  intro query node included found
  obtain ⟨old,oldPresent⟩ := present query included
  obtain ⟨next,nextPresent,tag,exposed⟩ := attach_metadata tree index parent parentNode newNode vacant parentPresent query old oldPresent
  have equal := Option.some.inj (found.symm.trans nextPresent)
  rw [equal,tag]
  exact bound query old included oldPresent

theorem exposed_update (tree : BorrowTree) (maximum : BorTag) (bound : ExposedBound tree maximum)
    (index : UniIndex) (old next : TreeNode) (present : tree.nodes.get index = some old)
    (tag : next.tag = old.tag) (flag : next.isExposed = old.isExposed) :
    ExposedBound {tree with nodes := tree.nodes.insert index next} maximum := by
  intro query node found exposed
  by_cases same : query = index
  · subst query
    change (tree.nodes.insert index next).get index = some node at found
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    rw [tag]
    exact bound index old present (flag ▸ exposed)
  · change (tree.nodes.insert index next).get query = some node at found
    rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
    exact bound query node found exposed

theorem exposed_attach (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false) (maximum : BorTag) (bound : ExposedBound tree maximum) :
    ExposedBound {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode} maximum := by
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;contradiction
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  exact exposed_update _ maximum (exposed_insert_hidden tree maximum bound index newNode hidden)
    parent parentNode {parentNode with children := parentNode.children.push index} parentAfter rfl rfl

theorem support_sifa (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (maximum : BorTag) (support : UniIndex → Prop)
    (present : ∀ query,support query → ∃ node,tree.nodes.get query = some node)
    (bound : SupportBound tree maximum support) :
    SupportBound (sourceUpdateSifa tree start strongest).1 maximum support := by
  intro query node included found
  obtain ⟨old,oldPresent⟩ := present query included
  obtain ⟨next,nextPresent,tag,_,_,_,_⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields tree start strongest query old oldPresent
  have equal := Option.some.inj (found.symm.trans nextPresent)
  rw [equal,tag]
  exact bound query old included oldPresent

theorem exposed_sifa (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (maximum : BorTag) (bound : ExposedBound tree maximum) :
    ExposedBound (sourceUpdateSifa tree start strongest).1 maximum := by
  intro query node found exposed
  have shape := GeneralBorrowSifaView.preserves tree start strongest
  obtain ⟨old,oldPresent,tag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields _ tree shape.symm query node found
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure tree _
    (GeneralBorrowFreshMetadataChildSifa.sifa_exposure tree start strongest) query
  change (sourceUpdateSifa tree start strongest).1.nodes.get query = some node at found
  rw [found,oldPresent] at flags
  have oldExposed : old.isExposed = true := by simpa only [Option.map_some,exposed,Option.some.injEq] using flags.symm
  rw [←tag]
  exact bound query old oldPresent oldExposed
end DuplicatePrefix.GeneralBorrowFreshRootScopedBounds
