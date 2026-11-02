import duplicate_prefix.GeneralBorrowAuthorizationMetadata
import duplicate_prefix.GeneralBorrowSifaWritableFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildSifa

namespace DuplicatePrefix.GeneralBorrowSharedAuthorizationSifaDepth
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Full callback authorization survives actual ancestor SIFA on any other
component, with both arbitrary cutoff kinds and every legal residual mask.
The only separation input is absence of physical parent paths from support. -/
theorem at_row (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
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
  let nextDepth := GeneralBorrowFreshMetadata.parent_depth tree after shape depth
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

end DuplicatePrefix.GeneralBorrowSharedAuthorizationSifaDepth
