import duplicate_prefix.GeneralBorrowPartitionState
import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowGeneratedReuseStarShape

namespace DuplicatePrefix.GeneralBorrowZeroDefaultConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshDefaultChild DuplicatePrefix.GeneralBorrowFreshGraph
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- The zero-length inside map has no segments. The real constructor still
allocates a tag/node, attaches it, and performs the ancestor SIFA update. -/
theorem exact (tree : BorrowTree) (parentTag newTag : BorTag) (parent index : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inserted : tree.tagMapping.insert newTag = .Inserted mapping index)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (parentAfter : (tree.nodes.insert index (child newTag parent)).get parent = some parentNode)
    (offset : UInt64) :
    tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false =
      ⟨(sourceUpdateSifa
        { (attached tree index parent parentNode (child newTag parent)) with tagMapping := mapping }
        parent .Read).1,
       (sourceUpdateSifa
        { (attached tree index parent parentNode (child newTag parent)) with tagMapping := mapping }
        parent .Read).2⟩ := by
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [tagged,Option.map_some,Bool.false_eq_true,↓reduceIte]
  simp only [Permission.isInitial,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  simp only [child] at parentAfter
  rw [parentAfter]
  simp only [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes,beq_self_eq_true,↓reduceIte,
    ←Array.forIn_toList,List.forIn_nil,pure]
  dsimp only [attached,attachedNodes,child]

/-- Append completion and exact tree for the actual zero-length Default reservation
constructor. No range map success or materialization is assumed or performed. -/
theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295) (offset : UInt64) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let stage := { (attached tree index parent parentNode (child newTag parent)) with
      tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩ }
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false).outcome = .ok () ∧
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false).tree = (sourceUpdateSifa stage parent .Read).1 := by
  dsimp only
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩
  have endEq : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have notParent := parent_not_fresh tree.nodes index parent parentNode endEq present
  have parentAfter := (append_get_other tree.nodes index parent (child newTag parent) endEq notParent).trans present
  have raw := exact tree parentTag newTag parent index parentNode mapping
    (GeneralBorrowTagMap.insert_append tree.tagMapping newTag fresh noFree fits) tagged parentAfter offset
  rw [raw]
  refine ⟨?_,rfl⟩
  simpa only [attached,attachedNodes,mapping] using
    sifa_after_attach {tree with tagMapping := mapping} depth index parent parentNode (child newTag parent) endEq present rfl .Read

/-- Vacant-slot reuse completion and exact tree for a real zero-length Default reservation
constructor. The outside reservation node is real even though no inside state exists. -/
theorem reuse (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent index : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (available : tree.tagMapping.deassigned.back? = some index)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (slack : depth.depth parent < tree.nodes.size) (offset : UInt64) :
    let stage := { (attached tree index parent parentNode (child newTag parent)) with
      tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩ }
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false).outcome = .ok () ∧
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false).tree = (sourceUpdateSifa stage parent .Read).1 := by
  dsimp only
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩
  have notParent := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant present
  have parentAfter := (GeneralBorrowFreshLocation.get_other tree.nodes index parent (child newTag parent) notParent).trans present
  have raw := exact tree parentTag newTag parent index parentNode mapping
    (GeneralBorrowTagMap.insert_free tree.tagMapping newTag fresh index available) tagged parentAfter offset
  rw [raw]
  refine ⟨?_,rfl⟩
  simpa only [attached,attachedNodes,mapping] using
    GeneralBorrowFreshReuseNode.sifa_after_attach {tree with tagMapping := mapping} depth index parent parentNode
      (child newTag parent) bounded vacant present rfl slack .Read

end DuplicatePrefix.GeneralBorrowZeroDefaultConstructor
