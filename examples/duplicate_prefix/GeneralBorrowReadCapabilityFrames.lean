import duplicate_prefix.GeneralBorrowReadCapabilityNormal
import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
namespace DuplicatePrefix.GeneralBorrowReadCapabilityFrames
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowPresence
open DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem canonical (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (root : Nat)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (rootValid : root < (source_normal_projection tree location protections).topology.nodes.size)
    (parentless : (source_normal_projection tree location protections).topology.nodes[root].parent = none)
    (path : Desc (source_normal_projection tree location protections).topology root anchor.toNat)
    (authorization : DuplicatePrefixNormalKind.Capability tree location protections anchor .Read) :
    ∃ next : DuplicatePrefixNormalKind.Capability tree location protections anchor .Read,
      next.component.support = Desc (source_normal_projection tree location protections).topology root := by
  have rootIncluded := GeneralBorrowNormalComponentNormalization.contains_ancestor _ anchor.toNat authorization.component root anchor.toNat path authorization.component.anchor
  let chosen := GeneralBorrowExposedScopedNormalRoot.component
    (source_normal_projection tree location protections).topology forest root anchor.toNat rootValid parentless path
  refine ⟨{component := chosen, permissions := ?_}, rfl⟩
  intro index supported valid
  exact authorization.permissions index
    (GeneralBorrowNormalComponentNormalization.contains_descendant _ forest anchor.toNat authorization.component root index supported rootIncluded) valid

theorem normal_framed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections anchor .Read)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (callbackKind : AccessKind) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (callback : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections other rootPosition maximum callbackKind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let after := (tree.performNormalAccessAt location anchor .Read protections mode).location
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
    (∀ index, support index → after.perms.get index = location.perms.get index) ∧
    Snapshot tree after protections other rootPosition maximum callbackKind support ∧
    (∀ index node, tree.nodes.get index = some node →
      other ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) index →
      after.perms.get index = location.perms.get index) := by
  let topology := (source_normal_projection tree location protections).topology
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode anchorPresent
  have selectedPath := GeneralBorrowPhysicalRootPath.selected_desc topology forest anchor.toNat selected.toNat geometry.1 rootPath
  have terminal := GeneralBorrowTerminal.ancestor_terminal topology forest anchor.toNat geometry.1
  have lastEq : (topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath]
    rfl
  rw [lastEq] at terminal
  have selectedParentless : (topology.nodes[selected.toNat]'selectedPath.valid.1).parent = none := by
    simpa only [nodeData,Array.getElem?_eq_getElem selectedPath.valid.1,Option.getD_some] using terminal
  obtain ⟨canonical,canonicalSupport⟩ := canonical tree location protections
    anchor selected.toNat forest selectedPath.valid.1 selectedParentless selectedPath normal
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat .Read canonical.component := by
    intro index included bounded
    have size : topology.nodes.size = tree.nodes.data.size := by
      unfold topology
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact canonical.permissions index included (by rw [←size];exact bounded)
  have actual := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections anchor .Read mode
    depth formed.children anchorNode anchorPresent forest canonical.component owned coherent
  obtain ⟨otherNode,otherPresent,otherParent⟩ := formed.rootNodes other otherMember
  have otherValid : other.toNat < topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes other otherNode otherPresent
    unfold topology
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  have otherProjection := projection_topology_node tree location protections other.toNat other otherNode rfl otherPresent
  change (topology.nodes[other.toNat]?.getD ⟨none,[]⟩) = _ at otherProjection
  simp only [Array.getElem?_eq_getElem otherValid,Option.getD_some] at otherProjection
  have otherParentless : (topology.nodes[other.toNat]'otherValid).parent = none := by
    rw [otherProjection]
    simp only [otherParent,Option.map_none]
  have componentSlots : ∀ index node, tree.nodes.get index = some node →
      other ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) index →
      (tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get index = location.perms.get index := by
    intro index node present member
    have physicalPath := GeneralBorrowWildcardControlWitness.path_of_walk tree depth other index node present _ member
    have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections other index physicalPath
    apply GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor .Read mode canonical.component index node present
    intro contained
    rw [canonicalSupport] at contained
    apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology selected.toNat other.toNat index.toNat
      selectedPath.valid.1 otherValid selectedParentless otherParentless _ contained projectedPath
    intro same
    exact different (GeneralBorrowNodeUpdate.index_injective selected other same)
  have slotFrame : ∀ index, support index →
      (tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get index = location.perms.get index := by
    intro index included
    obtain ⟨node,present⟩ := callback.present index included
    apply componentSlots index node present
    apply callback.covers index included (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)
    simp [GeneralBorrowExposureAncestorFold.walk]
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections other rootPosition maximum callbackKind support callback coherent short
  exact ⟨actual.1,actual.2.1,actual.2.2,slotFrame,
    GeneralBorrowRootLocalCounterFrame.snapshot tree location _ protections other rootPosition maximum callbackKind support snapshot coherent actual.2.2 callback.covers componentSlots slotFrame,componentSlots⟩


theorem after_normal_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections anchor .Read)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (callbackKind : AccessKind) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (callback : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections other rootPosition maximum callbackKind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let after := (tree.performNormalAccessAt location anchor .Read protections mode).location
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
    (∀ index, support index → after.perms.get index = location.perms.get index) ∧
    Snapshot tree after protections other rootPosition maximum callbackKind support ∧
    DuplicatePrefixResidualSupportAuthorization.Authorization tree after protections other rootPosition maximum callbackKind support := by
  obtain ⟨complete,ok,afterCoherent,slots,snapshot,componentSlots⟩ := normal_framed tree location protections formed anchor selected other anchorNode anchorPresent normal rootPath otherMember different callbackKind rootPosition maximum support callback coherent short mode
  exact ⟨complete,ok,afterCoherent,slots,snapshot,
    GeneralBorrowRootLocalAuthorization.authorization tree location _ protections other rootPosition maximum callbackKind support callback componentSlots⟩
private theorem converted_nat (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) : index.toNat = position := by
  unfold UniIndex.ofNat? at converted
  split at converted
  next bounded => cases converted;simp only [UniIndex.toNat];exact Nat.mod_eq_of_lt (by omega)
  next => contradiction

theorem after_callback (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixNormalKind.Capability tree before protections anchor .Read)
    (rootPath : ((source_normal_projection tree before protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (support : UniIndex → Prop)
    (supportPresent : ∀ query, support query → ∃ node, tree.nodes.get query = some node)
    (covers : ∀ query, support query → GeneralBorrowExposureCardinality.Covers tree.nodes other query)
    (outside : ∀ query, ¬support query → after.perms.get query = before.perms.get query) :
    ∃ next : DuplicatePrefixNormalKind.Capability tree after protections anchor .Read,
      next.component.support = Desc (source_normal_projection tree before protections).topology selected.toNat := by
  let topology := (source_normal_projection tree before protections).topology
  obtain ⟨forest⟩ := formed.forest before protections
  obtain ⟨depth⟩ := formed.depth
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree before protections anchor anchorNode anchorPresent
  have selectedPath := GeneralBorrowPhysicalRootPath.selected_desc topology forest anchor.toNat selected.toNat geometry.1 rootPath
  have terminal := GeneralBorrowTerminal.ancestor_terminal topology forest anchor.toNat geometry.1
  have lastEq : (topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  rw [lastEq] at terminal
  have selectedParentless : (topology.nodes[selected.toNat]'selectedPath.valid.1).parent = none := by
    simpa only [nodeData,Array.getElem?_eq_getElem selectedPath.valid.1,Option.getD_some] using terminal
  obtain ⟨canonical,canonicalSupport⟩ := canonical tree before protections anchor selected.toNat
    forest selectedPath.valid.1 selectedParentless selectedPath normal
  obtain ⟨otherNode,otherPresent,otherParent⟩ := formed.rootNodes other otherMember
  have otherValid : other.toNat < topology.nodes.size := by
    have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes other otherNode otherPresent
    unfold topology
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bound
  have projected := projection_topology_node tree before protections other.toNat other otherNode rfl otherPresent
  change (topology.nodes[other.toNat]?.getD ⟨none,[]⟩) = _ at projected
  simp only [Array.getElem?_eq_getElem otherValid,Option.getD_some] at projected
  have otherParentless : (topology.nodes[other.toNat]'otherValid).parent = none := by rw [projected];simp only [otherParent,Option.map_none]
  have slots : ∀ position, canonical.component.support position → ∀ query, UniIndex.ofNat? position = some query →
      after.perms.get query = before.perms.get query := by
    intro position inside query converted
    apply outside query
    intro operated
    obtain ⟨queryNode,present⟩ := supportPresent query operated
    have walk := covers query operated (query,queryNode) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query queryNode).mpr present)
      (by simp [GeneralBorrowExposureAncestorFold.walk])
    have path := GeneralBorrowPhysicalRootPath.projection_desc tree before protections other query
      (GeneralBorrowWildcardControlWitness.path_of_walk tree depth other query queryNode present _ walk)
    have equal := converted_nat position query converted
    have selectedDesc : Desc topology selected.toNat query.toNat := by rw [equal];rw [canonicalSupport] at inside;exact inside
    apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology selected.toNat other.toNat query.toNat
      selectedPath.valid.1 otherValid selectedParentless otherParentless _ selectedDesc path
    intro same
    exact different (GeneralBorrowNodeUpdate.index_injective selected other same)
  refine ⟨{component := canonical.component,permissions := ?_},canonicalSupport⟩
  intro position included valid
  obtain ⟨state,present,compatible⟩ := canonical.permissions position included valid
  refine ⟨state,?_,compatible⟩
  rw [GeneralBorrowNormalOtherCallbackFrame.projection_frame tree before after protections position valid (slots position included)]
  exact present
end DuplicatePrefix.GeneralBorrowReadCapabilityFrames
