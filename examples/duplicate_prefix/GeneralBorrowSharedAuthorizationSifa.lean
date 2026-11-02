import duplicate_prefix.GeneralBorrowAuthorizationMetadata
import duplicate_prefix.GeneralBorrowSifaWritableFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildSifa

namespace DuplicatePrefix.GeneralBorrowSharedAuthorizationSifa
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Full callback authorization survives actual ancestor SIFA on any other
component, with both arbitrary cutoff kinds and every legal residual mask.
The only separation input is absence of physical parent paths from support. -/
theorem at_row (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (start : UniIndex) (startNode : TreeNode) (present : tree.nodes.get start = some startNode)
    (strongest : IdempotentForeignAccess) (protections : ProtectedTags)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree (tree.locations.entries[position]'valid).data protections root rootPosition maximum kind support)
    (outside : ∀ query,support query → ¬Path tree query start) :
    let after := (sourceUpdateSifa tree start strongest).1
    ∃ nextValid : position < after.locations.entries.size,
      Authorization after (after.locations.entries[position]'nextValid).data protections root rootPosition maximum kind support := by
  let after := (sourceUpdateSifa tree start strongest).1
  have shape : treeShape after = treeShape tree := GeneralBorrowSifaView.preserves tree start strongest
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have lengths := congrArg Array.size ranges
  simp only [Array.size_map] at lengths
  have nextValid : position < after.locations.entries.size := by omega
  refine ⟨nextValid,?_⟩
  have locationShapeSame : locationShape (after.locations.entries[position]'nextValid).data =
      locationShape (tree.locations.entries[position]'valid).data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem nextValid,Option.map_some] at known
    exact congrArg Prod.snd (Option.some.inj known)
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨nextDepth⟩ := (GeneralBorrowStructuralHistoryState.graph_shape tree after shape formed).depth
  have size : tree.nodes.size ≤ after.nodes.size := by
    rw [GeneralBorrowFreshMetadata.node_size tree after shape]
    exact Nat.le_refl _
  have exactFrame (query : UniIndex) (included : support query) :=
    GeneralBorrowSifaOutsidePath.frame tree depth start startNode present query (outside query included) strongest
  refine GeneralBorrowAuthorizationMetadata.transport tree after _ _ protections depth nextDepth size ?_ ?_
    root rootPosition maximum kind support old ?_ ?_
  · intro index node found
    obtain ⟨next,lookup,tag,parent,children,permission,exposure⟩ :=
      GeneralBorrowFreshMetadataChildSifa.node_fields tree start strongest index node found
    refine ⟨next,lookup,parent,tag,exposure,?_⟩
    have state := GeneralBorrowSifaWritableFrame.effective_shape
      (tree.locations.entries[position]'valid).data (after.locations.entries[position]'nextValid).data
      index node next locationShapeSame permission
    exact congrArg Prod.fst state
  · intro index next found exposed
    obtain ⟨node,lookup,_⟩ := GeneralBorrowFreshMetadata.node_fields after tree shape.symm index next found
    exact ⟨node,lookup⟩
  · intro query included
    exact congrArg Prod.fst (exactFrame query included)
  · intro query included
    have frames := congrArg Prod.snd (exactFrame query included)
    change after.locations.entries.map (fun segment => (segment.range,segment.data.perms.get query)) =
      tree.locations.entries.map (fun segment => (segment.range,segment.data.perms.get query)) at frames
    have known := congrArg (fun rows => rows[position]?) frames
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem nextValid,Option.map_some] at known
    exact congrArg Prod.snd (Option.some.inj known)

/-- Opposite physical roots provide the precise path exclusion required by
SIFA from raw parent/root data and the original complete authorization. -/
theorem other_outside (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (selected other parent : UniIndex) (parentNode : TreeNode)
    (present : tree.nodes.get parent = some parentNode)
    (selectedMember : selected ∈ tree.roots.toList) (otherMember : other ∈ tree.roots.toList)
    (different : selected ≠ other)
    (selectedPath : selected ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) parent)
    (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections other position maximum kind support) :
    ∀ query,support query → ¬Path tree query parent := by
  intro query included path
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨node,found⟩ := old.present query included
  have rootPath := GeneralBorrowWildcardControlWitness.path_of_covers tree depth other query node found (old.covers query included)
  have otherPath := (GeneralBorrowSharedAuthorizationGeometry.path_trans rootPath path).walk depth
  exact GeneralBorrowRootLocalCounterFrame.components_disjoint tree location protections formed selected other parent parentNode
    present selectedMember otherMember different selectedPath otherPath

/-- Operational other-root endpoint: path exclusion is derived internally
from physical root separation and the initial raw authorization. -/
theorem other_at_row (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (parent : UniIndex) (parentNode : TreeNode) (present : tree.nodes.get parent = some parentNode)
    (strongest : IdempotentForeignAccess) (protections : ProtectedTags)
    (selected other : UniIndex) (selectedMember : selected ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (selectedPath : selected ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) parent)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree (tree.locations.entries[position]'valid).data protections other rootPosition maximum kind support) :
    let after := (sourceUpdateSifa tree parent strongest).1
    ∃ nextValid : position < after.locations.entries.size,
      Authorization after (after.locations.entries[position]'nextValid).data protections other rootPosition maximum kind support := by
  apply at_row tree formed parent parentNode present strongest protections position valid other rootPosition maximum kind support old
  exact other_outside tree formed _ protections selected other parent parentNode present selectedMember otherMember different
    selectedPath rootPosition maximum kind support old

end DuplicatePrefix.GeneralBorrowSharedAuthorizationSifa
