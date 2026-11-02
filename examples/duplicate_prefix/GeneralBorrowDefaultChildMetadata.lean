import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowStructuralHistoryDefault
namespace DuplicatePrefix.GeneralBorrowDefaultChildMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildDefaultSlot
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual allocator append or reuse determines the child index and full path
extension, while every old node keeps its tag. No geometry is supplied by callers. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let after := result tree parentTag newTag offset len
    ∃ child, after.indexOfTag newTag = some child ∧
      (∃ node, after.nodeAt child = some node ∧ node.tag = newTag ∧ node.isExposed = false) ∧
      (∀ oldLocation newLocation protections,
        GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree oldLocation protections).topology
          (source_normal_projection after newLocation protections).topology parent.toNat child.toNat) ∧
      (∀ query oldNode, tree.nodeAt query = some oldNode →
        ∃ next, after.nodeAt query = some next ∧ next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed) := by
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  have metadata := build tree rank runtime.formed.children runtime.formed.covered parentTag newTag parent parentNode
    tagged present fresh slot offset len nonzero runtime.formed.well runtime.formed.fits bounds
  refine ⟨index slot,metadata.lookup,metadata.node,?_,?_⟩
  · intro oldLocation newLocation protections
    obtain ⟨forest⟩ := runtime.formed.forest oldLocation protections
    cases slot with
    | append noFree aligned fits =>
      let input : GeneralBorrowFreshMetadataChildDefault.Input :=
        ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
          noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
      have attached := GeneralBorrowFreshSharedPaths.of_append _ _ _
        ((GeneralBorrowFreshMetadataChildDefault.append input).extension oldLocation newLocation protections) forest
      have size : (source_normal_projection tree oldLocation protections).topology.nodes.size = tree.nodes.data.size := by
        unfold_general_projection
        unfold_general_topology
        simp only [Array.size_map]
      rw [size,←GeneralBorrowFreshMetadataChildDefault.at_end input] at attached
      exact attached
    | reuse child available valid vacant slack =>
      let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
        ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
          child,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
      exact GeneralBorrowFreshSharedPaths.of_reuse _ _ _ _
        ((GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).extension oldLocation newLocation protections) forest
  · intro query oldNode oldPresent
    exact GeneralBorrowFreshMetadataChildDefaultOld.of_slot tree rank runtime.formed.children runtime.formed.covered parentTag newTag parent parentNode
      tagged present fresh slot offset len nonzero runtime.formed.well bounds query oldNode oldPresent
end DuplicatePrefix.GeneralBorrowDefaultChildMetadata
