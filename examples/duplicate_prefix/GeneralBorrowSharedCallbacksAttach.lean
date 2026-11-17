import duplicate_prefix.GeneralBorrowSharedCallbacksData
import duplicate_prefix.GeneralBorrowSharedAuthorizationSifa
import duplicate_prefix.GeneralBorrowFreshMetadataChildAttach

namespace DuplicatePrefix.GeneralBorrowSharedCallbacksAttach
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowFreshNode GeneralBorrowNodeUpdate
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixResidualSupportAuthorization GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert

/-- Both old callback capabilities, plus the graph separation needed by the
actual ancestor-SIFA loop. This helper data is derived from the initial Row. -/
def Framed (tree : BorrowTree) (protections : ProtectedTags) (parent selected : UniIndex)
    (maximum : Option BorTag) (location : LocationTree) : Prop :=
  ∀ position,(valid : position < tree.roots.size) → some selected ≠ some tree.roots[position] →
    ∃ support,Authorization tree location protections tree.roots[position] position maximum .Read support ∧
      Authorization tree location protections tree.roots[position] position maximum .Write support ∧
      ∀ query,support query → query ∉ walk tree.nodes (tree.nodes.size+1) parent

theorem parents (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode) :
    ∀ old oldNode,tree.nodes.get old = some oldNode →
      ∃ next,(attachedNodes tree.nodes index parent parentNode newNode).get old = some next ∧ next.parent = oldNode.parent := by
  intro old oldNode found
  have different : parent ≠ index := by intro same;rw [same,vacant] at parentPresent;cases parentPresent
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  have neqIndex : old ≠ index := by intro same;rw [same,vacant] at found;cases found
  by_cases isParent : old = parent
  · subst old
    have equal := Option.some.inj (found.symm.trans parentPresent)
    subst oldNode
    exact ⟨{parentNode with children := parentNode.children.push index},
      insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter,rfl⟩
  · refine ⟨oldNode,?_,rfl⟩
    unfold attachedNodes
    rw [GeneralBorrowFreshLocation.get_other _ parent old _ isParent,
      GeneralBorrowFreshLocation.get_other _ index old _ neqIndex,found]

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
    (old : DuplicatePrefixBorrowAuthorization.Row tree before protections (some parent) (some selected) maximum)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query) :
    Framed {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      protections parent selected maximum after := by
  obtain ⟨selectedMember,selectedPath⟩ := root_metadata tree formed before protections parent selected maximum parentNode parentPresent old
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

theorem context (tree : BorrowTree) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (parent selected : UniIndex) (maximum : Option BorTag)
    (old : Framed tree protections parent selected maximum location) :
    Framed {tree with tagMapping := mapping,locations := locations} protections parent selected maximum location := by
  intro position valid different
  obtain ⟨support,read,write,outside⟩ := old position valid different
  exact ⟨support,authorization_context tree mapping locations location protections _ _ _ _ support read,
    authorization_context tree mapping locations location protections _ _ _ _ support write,outside⟩

end DuplicatePrefix.GeneralBorrowSharedCallbacksAttach
