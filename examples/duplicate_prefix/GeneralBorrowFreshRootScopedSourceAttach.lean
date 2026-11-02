import duplicate_prefix.GeneralBorrowFreshRootScopedAttach
import duplicate_prefix.GeneralBorrowFreshRootScopedSource
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSourceAttach
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowFreshNode GeneralBorrowNodeUpdate
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization GeneralBorrowSharedCallbacksData
open GeneralBorrowFreshRootScopedAttach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem row (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode))
    (before after : LocationTree) (protections : ProtectedTags) (selected : UniIndex) (maximum : BorTag)
    (old : GeneralBorrowFreshRootScopedSource.Source tree before protections parent selected maximum)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query) :
    Framed {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      protections parent selected maximum after := by
  refine ⟨GeneralBorrowFreshRootScopedBounds.exposed_attach tree index parent parentNode newNode vacant parentPresent hidden maximum old.exposed,?_⟩
  obtain ⟨selectedMember,selectedPath⟩ := GeneralBorrowCallbackSource.metadata tree formed before protections parent selected (some maximum) parentNode parentPresent old.base
  intro position valid different
  have otherMember : tree.roots[position] ∈ tree.roots.toList :=
    Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨position,valid,rfl⟩)
  have unequal : selected ≠ tree.roots[position] := different
  obtain ⟨support,bounded,read,write⟩ := old.callbacks position valid different
  have notParent := GeneralBorrowSharedAuthorizationGeometry.other_not_parent tree formed before protections selected _ parent parentNode
    parentPresent selectedMember otherMember unequal selectedPath position (some maximum) .Read support read
  have nextRead := GeneralBorrowSharedAuthorizationGeometry.authorization tree depth index parent parentNode newNode vacant parentPresent
    hidden size nextDepth before after protections slots _ position (some maximum) .Read support read notParent
  have nextWrite := GeneralBorrowSharedAuthorizationGeometry.authorization tree depth index parent parentNode newNode vacant parentPresent
    hidden size nextDepth before after protections slots _ position (some maximum) .Write support write notParent
  have nextBound := GeneralBorrowFreshRootScopedBounds.support_attach tree index parent parentNode newNode vacant parentPresent maximum support read.present bounded
  refine ⟨support,nextBound,nextRead,nextWrite,?_⟩
  intro query included member
  have walks := GeneralBorrowExposureGraphTransport.walk_extension tree.nodes
    (attachedNodes tree.nodes index parent parentNode newNode) depth (parents tree index parent parentNode newNode vacant parentPresent)
    (tree.nodes.size+1) ((attachedNodes tree.nodes index parent parentNode newNode).size+1) parent parentNode parentPresent
    (by have := depth.bounded parent parentNode parentPresent;omega)
    (by have := depth.bounded parent parentNode parentPresent;omega)
  rw [walks] at member
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query parent parentNode parentPresent _ member
  exact GeneralBorrowSharedAuthorizationSifa.other_outside tree formed before protections selected _ parent parentNode parentPresent
    selectedMember otherMember unequal selectedPath position (some maximum) .Read support read query included path

end DuplicatePrefix.GeneralBorrowFreshRootScopedSourceAttach
