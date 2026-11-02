import duplicate_prefix.S03EmptySharedFrame
import duplicate_prefix.GeneralBorrowFreshParentTagOrder
import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.GeneralBorrowFreshRootScopedBounds
import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S03EmptySharedGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFreshRootSupportCutoff
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- Empty Shared and len argument construction preserves the runtime's raw
parent/tag order. The new-tag comparison is explicit initial data, later
derived from the monotone allocator resource. -/
theorem order {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag)
    (ordered : ParentTagOrder tree) (parentOrder : input.parentNode.tag.value ≤ tag.value) :
    ParentTagOrder input.after := by
  exact GeneralBorrowFreshParentTagOrder.staged_order tree input.depth ordered input.index input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present rfl parentOrder input.mapping tree.locations
    input.after (GeneralBorrowSifaView.preserves input.stage input.parent .Read)

/-- The initial runtime counter supplies the fresh edge comparison; callers
need no new ordering assumption about the generated child. -/
theorem fresh_order (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag global.nextPointerTag)
    (ordered : ParentTagOrder tree) : ParentTagOrder input.after := by
  apply order input ordered
  exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
    (GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime input.parent input.parentNode input.present)))

/-- Fresh zero-window children are hidden, so an old return-root cutoff still
bounds EVERY exposed node, even when later hidden descendants exceed it. -/
theorem exposed {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (maximum : BorTag)
    (bounded : ExposedBound tree maximum) : ExposedBound input.after maximum := by
  have attached := GeneralBorrowFreshRootScopedBounds.exposed_attach tree input.index input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present rfl maximum bounded
  have staged : ExposedBound input.stage maximum := attached
  exact GeneralBorrowFreshRootScopedBounds.exposed_sifa input.stage input.parent .Read maximum staged

/-- A hidden return root retains its root position, tag and parentless edge
through either allocator branch of both actual zero constructors. -/
theorem hidden_root {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (hidden : node.isExposed = false) (root : node.parent = none)
    (position : Nat) (valid : position < tree.roots.size) (atPosition : tree.roots[position] = index) :
    ∃ next, input.after.nodeAt index = some next ∧ next.tag = node.tag ∧
      next.isExposed = false ∧ next.parent = none ∧
      ∃ nextValid : position < input.after.roots.size, input.after.roots[position] = index := by
  obtain ⟨next,found,sameTag,parent,exposed⟩ := S03EmptySharedFrame.old_node input index node present
  have roots : input.after.roots = tree.roots :=
    GeneralBorrowFreshMetadata.roots input.stage input.after (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  refine ⟨next,found,sameTag,exposed.trans hidden,parent.trans root,?_,?_⟩
  · rw [roots]
    exact valid
  · simpa only [roots] using atPosition

/-- A return child distinct from the empty argument's constructor parent
remains a hidden parentless leaf, as required by wildcard restoration. -/
theorem old_leaf {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (different : index ≠ input.parent)
    (hidden : node.isExposed = false) (root : node.parent = none) (leaf : node.children = #[]) :
    ∃ next, input.after.nodeAt index = some next ∧ next.tag = node.tag ∧
      next.isExposed = false ∧ next.parent = none ∧ next.children = #[] := by
  have staged : input.stage.nodeAt index = some node := by
    have original : input.stage.nodeAt index = some (S04ZeroReadSharedAttach.liftNode input.parent input.index index node) :=
      S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present index node present
    simpa only [S04ZeroReadSharedAttach.liftNode,different,ite_false] using original
  obtain ⟨next,found,sameTag,parent,children,permission,exposed⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields input.stage input.parent .Read index node staged
  exact ⟨next,found,sameTag,exposed.trans hidden,parent.trans root,children.trans leaf⟩

/-- Existing caller protectors continue to name hidden nodes. Fresh Shared/len
nodes are themselves hidden, and SIFA never changes tags or exposure bits. -/
theorem hidden_frame {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (frame : FrameState)
    (hidden : S04ReturnReleaseParent.HiddenFrame tree frame) :
    S04ReturnReleaseParent.HiddenFrame input.after frame := by
  have staged : S04ReturnReleaseParent.HiddenFrame input.stage frame := by
    intro row member query node present sameTag
    have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes input.index input.parent input.parentNode input.vacant input.present
    change ((tree.nodes.insert input.index (GeneralBorrowFreshAnchor.sharedNode tag input.parent)).insert input.parent
      (GeneralBorrowFreshGraph.updatedParent input.parentNode input.index)).get query = some node at present
    by_cases fresh : query = input.index
    · subst query
      rw [GeneralBorrowFreshLocation.get_other _ input.parent input.index _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at present
      cases present
      rfl
    · by_cases parent : query = input.parent
      · subst query
        rw [GeneralBorrowFreshLocation.get_same] at present
        cases present
        exact hidden row member input.parent input.parentNode input.present sameTag
      · rw [GeneralBorrowFreshLocation.get_other _ input.parent query _ parent,
          GeneralBorrowFreshLocation.get_other _ input.index query _ fresh] at present
        exact hidden row member query node present sameTag
  intro row member query node present sameTag
  have shape := GeneralBorrowSifaView.preserves input.stage input.parent .Read
  obtain ⟨old,prior,oldTag,oldParent,oldChildren,oldPermission⟩ :=
    GeneralBorrowFreshMetadata.node_fields input.after input.stage shape.symm query node present
  obtain ⟨actual,found,tagEq,parent,children,permission,exposed⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields input.stage input.parent .Read query old prior
  have same := Option.some.inj (found.symm.trans present)
  subst actual
  exact exposed.trans (staged row member query old prior (oldTag.trans sameTag))

end DuplicatePrefix.S03EmptySharedGeometry
