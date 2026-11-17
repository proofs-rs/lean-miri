import duplicate_prefix.GeneralBorrowCallbackSource
import duplicate_prefix.GeneralBorrowSharedCallbacksAttach
namespace DuplicatePrefix.GeneralBorrowCallbackSourceAttach
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowFreshNode GeneralBorrowNodeUpdate
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization GeneralBorrowSharedCallbacksData
open GeneralBorrowCallbackSource GeneralBorrowSharedCallbacksAttach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert
/-- Exact shared attachment preserves every other-root full authorization and
derives its SIFA separation from the raw S01 selected physical-root path. -/
theorem row (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode))
    (before after : LocationTree) (protections : ProtectedTags) (selected : UniIndex) (maximum : Option BorTag)
    (old : Source tree before protections parent selected maximum)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query) :
    Framed {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      protections parent selected maximum after := by
  obtain ⟨selectedMember,selectedPath⟩ := GeneralBorrowCallbackSource.metadata tree formed before protections parent selected maximum parentNode parentPresent old
  intro position valid different
  have otherMember : tree.roots[position] ∈ tree.roots.toList :=
    Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨position,valid,rfl⟩)
  have unequal : selected ≠ tree.roots[position] := by intro same;exact different (congrArg some same)
  obtain ⟨support,read,write⟩ := old.callbacks position valid different
  have notParent := GeneralBorrowSharedAuthorizationGeometry.other_not_parent tree formed before protections selected _ parent parentNode
    parentPresent selectedMember otherMember unequal selectedPath position maximum .Read support read
  have nextRead := GeneralBorrowSharedAuthorizationGeometry.authorization tree depth index parent parentNode newNode vacant parentPresent
    hidden size nextDepth before after protections slots _ position maximum .Read support read notParent
  have nextWrite := GeneralBorrowSharedAuthorizationGeometry.authorization tree depth index parent parentNode newNode vacant parentPresent
    hidden size nextDepth before after protections slots _ position maximum .Write support write notParent
  refine ⟨support,nextRead,nextWrite,?_⟩
  intro query included member
  have walks := GeneralBorrowExposureGraphTransport.walk_extension tree.nodes
    (attachedNodes tree.nodes index parent parentNode newNode) depth (parents tree index parent parentNode newNode vacant parentPresent)
    (tree.nodes.size+1) ((attachedNodes tree.nodes index parent parentNode newNode).size+1) parent parentNode parentPresent
    (by have := depth.bounded parent parentNode parentPresent;omega)
    (by have := depth.bounded parent parentNode parentPresent;omega)
  rw [walks] at member
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query parent parentNode parentPresent _ member
  exact GeneralBorrowSharedAuthorizationSifa.other_outside tree formed before protections selected _ parent parentNode parentPresent
    selectedMember otherMember unequal selectedPath position maximum .Read support read query included path

end DuplicatePrefix.GeneralBorrowCallbackSourceAttach
