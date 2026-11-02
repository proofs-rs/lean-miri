import duplicate_prefix.GeneralBorrowProtectedSiblingPartialFunctionHistory
import duplicate_prefix.GeneralBorrowSharedRootBankState
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingBankSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProjection GeneralBorrowProtectedSiblingPartialFunctionHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Unheld old reservations need not be Frozen. Root Write ownership supplies
both the bank's root Read and the retained root-only writable label. -/
theorem combined (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (owned : GeneralBorrowRange.LocationOwned tree {} root .Write location) :
    GeneralBorrowFreshReleaseMixed.Combined tree {} root (GeneralBorrowSharedRootLabel.writable root) location := by
  have read := (GeneralBorrowFreshMixedChild.write_combined tree location {} root owned).1
  refine ⟨read,?_⟩
  intro position valid
  by_cases same : position = root.toNat
  · obtain ⟨state,present,permission⟩ := owned.2.permissions position (by rw [←owned.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,GeneralBorrowSharedRootLabel.writable,same] using permission⟩
  · obtain ⟨state,present,permission⟩ := read.2.permissions position (by rw [←read.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,GeneralBorrowSharedRootLabel.writable,same] using permission⟩

theorem parentless {bytes windows} (h : History bytes windows) (nonzero : bytes ≠ 0) : h.rootNode.parent = none := by
  have inside : (0 : UInt64).toNat < h.output.tree.locations.size.bytes.toNat := by
    rw [h.capacity]
    exact UInt64.lt_iff_toNat_lt.mp (UInt64.pos_iff_ne_zero.mpr nonzero)
  obtain ⟨position,valid,contains⟩ := GeneralRangeMapGeometry.covered h.output.tree.locations h.well 0 inside
  obtain ⟨⟨forest⟩,owner⟩ := h.owned position valid
  let location := h.output.tree.locations.entries[position].data
  let normal := source_normal_projection h.output.tree location h.output.ended.protectedTags
  have anchorValid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor h.output.tree location h.output.ended.protectedTags
    GeneralBorrowFullSharedSeed.root h.rootNode h.rootPresent
  have lastRoot := GeneralBorrowTerminal.ancestor_root_present normal.topology forest (GeneralBorrowGraph.Present h.output.tree)
    (GeneralBorrowGraph.parents_closed h.output.tree location h.output.ended.protectedTags h.depth)
    GeneralBorrowFullSharedSeed.root.toNat GeneralBorrowFullSharedSeed.root.toNat anchorValid
    ⟨GeneralBorrowFullSharedSeed.root,h.rootNode,rfl,h.rootPresent⟩
    (fun index _ found parentless => GeneralBorrowGraph.unique_root h.output.tree location h.output.ended.protectedTags
      GeneralBorrowFullSharedSeed.root h.roots h.covered index found parentless)
  have terminal := GeneralBorrowTerminal.ancestor_terminal normal.topology forest GeneralBorrowFullSharedSeed.root.toNat anchorValid
  rw [lastRoot] at terminal
  change ((normal.topology.nodes[GeneralBorrowFullSharedSeed.root.toNat]?).getD ⟨none,[]⟩).parent = none at terminal
  rw [projection_topology_node h.output.tree location h.output.ended.protectedTags GeneralBorrowFullSharedSeed.root.toNat
    GeneralBorrowFullSharedSeed.root h.rootNode rfl h.rootPresent] at terminal
  cases edge : h.rootNode.parent with
  | none => rfl
  | some parent => simp only [edge,Option.map_some,Option.getD_some] at terminal;cases terminal

theorem path {bytes windows} (h : History bytes windows) (nonzero : bytes ≠ 0) (location : LocationTree) :
    (source_normal_projection h.output.tree location {}).topology.ancestorPath GeneralBorrowFullSharedSeed.root.toNat = [GeneralBorrowFullSharedSeed.root.toNat] := by
  have edge := parentless h nonzero
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection h.output.tree location {}).topology GeneralBorrowFullSharedSeed.root.toNat).parent = none := by
    change ((source_normal_projection h.output.tree location {}).topology.nodes[GeneralBorrowFullSharedSeed.root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node h.output.tree location {} GeneralBorrowFullSharedSeed.root.toNat GeneralBorrowFullSharedSeed.root h.rootNode rfl h.rootPresent]
    simp only [edge,Option.map_none,Option.getD_some]
  change sourceAncestorPath (source_normal_projection h.output.tree location {}).topology
    (source_normal_projection h.output.tree location {}).topology.nodes.size GeneralBorrowFullSharedSeed.root.toNat = _
  cases (source_normal_projection h.output.tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- The same actual released tree becomes a root-only selectable bank; its
old Reserved children and all sparse permissions remain in the real tree. -/
def of_history {bytes windows} (h : History bytes windows) (nonzero : bytes ≠ 0) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ bytes.toNat) (room : h.output.tree.nodes.size+4 ≤ 4294967295) :
    GeneralBorrowSharedRootBankState.State GeneralBorrowFullSharedSeed.root h.rootNode.tag offset len := by
  let resources : GeneralBorrowRecursiveSharedResources.Resources h.output.tree GeneralBorrowFullSharedSeed.root := {
    depth := h.depth,children := h.children,covered := h.covered,roots := h.roots,allocator := h.allocator,clean := h.vacant,well := h.well,room := room }
  have all : Every (GeneralBorrowRange.LocationOwned h.output.tree {} GeneralBorrowFullSharedSeed.root .Write) h.output.tree.locations := by
    simpa only [h.empty] using h.owned
  exact {
    bank := {
      tree := h.output.tree,resources := resources,handles := [GeneralBorrowFullSharedSeed.root],
      present := by intro index member;have same := List.mem_singleton.mp member;subst index;exact ⟨h.rootNode,h.rootPresent⟩,
      bounds := by rw [h.capacity];exact bounds,
      owned := by
        intro index member position valid _ _ _
        have same := List.mem_singleton.mp member
        subst index
        exact (GeneralBorrowFreshMixedChild.write_combined _ _ _ _ (all position valid)).1 }
    rootMember := by simp
    rootPresent := ⟨h.rootNode,h.rootPresent,rfl⟩
    rootPath := path h nonzero
    paths := by
      intro index member location
      have same := List.mem_singleton.mp member
      subst index
      rw [path h nonzero]
      simp
    owned := by
      intro index member position valid _ _ _
      have same := List.mem_singleton.mp member
      subst index
      exact combined _ _ _ (all position valid) }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingBankSeed
