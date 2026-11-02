import duplicate_prefix.GeneralBorrowNormalOtherRootSnapshot
namespace DuplicatePrefix.GeneralBorrowNormalOtherCallbackFrame
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowPresence
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem converted_nat (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) : index.toNat = position := by
  unfold UniIndex.ofNat? at converted
  split at converted
  next bounded => cases converted;simp only [UniIndex.toNat,UInt32.toNat_ofNat];exact Nat.mod_eq_of_lt (by omega)
  next => contradiction

/-- Source projection depends only on the one convertible physical permission
slot. A nonconvertible position has no such slot and uses the same defaults. -/
theorem projection_frame (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (position : Nat) (valid : position < tree.nodes.data.size)
    (slots : ∀ query, UniIndex.ofNat? position = some query → after.perms.get query = before.perms.get query) :
    (source_normal_projection tree after protections).stateAt position =
      (source_normal_projection tree before protections).stateAt position := by
  cases converted : UniIndex.ofNat? position with
  | none =>
    unfold_general_projection
    simp only [NormalTreeState.stateAt,Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted]
  | some query =>
    have slot := slots query converted
    unfold_general_projection
    simp only [NormalTreeState.stateAt,Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted,slot]

/-- Pure data transport after arbitrary changes outside another physical root.
An arbitrary larger Normal component is restricted internally to the selected
root's canonical descendants. No operation/cache/permission-profile condition,
ParentTagOrder, or selected-component separation premise is supplied. -/
theorem transport (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree before protections anchor)
    (rootPath : ((source_normal_projection tree before protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (support : UniIndex → Prop)
    (supportPresent : ∀ query, support query → ∃ node, tree.nodes.get query = some node)
    (covers : ∀ query, support query → GeneralBorrowExposureCardinality.Covers tree.nodes other query)
    (outside : ∀ query, ¬support query → after.perms.get query = before.perms.get query) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal tree after protections anchor,
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
  obtain ⟨canonical,canonicalSupport⟩ := GeneralBorrowNormalComponentNormalization.canonical tree before protections anchor selected.toNat
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
  intro kind position included valid
  obtain ⟨state,present,compatible⟩ := canonical.permissions kind position included valid
  refine ⟨state,?_,compatible⟩
  rw [projection_frame tree before after protections position valid (slots position included)]
  exact present
end DuplicatePrefix.GeneralBorrowNormalOtherCallbackFrame
