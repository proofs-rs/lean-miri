import duplicate_prefix.GeneralBorrowCompatibleNormalReadFrame
import duplicate_prefix.GeneralBorrowPhysicalRootPath
import duplicate_prefix.GeneralBorrowRootLocalCounterFrame
import duplicate_prefix.GeneralBorrowRootLocalAuthorization
import duplicate_prefix.GeneralBorrowSnapshotReadState
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.GeneralBorrowTerminal
namespace DuplicatePrefix.GeneralBorrowNormalOtherRootSnapshot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowPresence
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- A real normal Read OR Write transports an arbitrary other physical root's
Read OR Write snapshot, for any cutoff. Only root-local counters are framed.
The actual component, separation and successful operation are derived from
initial normal authorization and GraphState. -/
theorem after_normal_framed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (normalKind callbackKind : AccessKind) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (callback : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections other rootPosition maximum callbackKind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let after := (tree.performNormalAccessAt location anchor normalKind protections mode).location
    (tree.performNormalAccessAt location anchor normalKind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor normalKind protections mode).outcome = .ok () ∧
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
  obtain ⟨canonical,canonicalSupport⟩ := GeneralBorrowNormalComponentNormalization.canonical tree location protections
    anchor selected.toNat forest selectedPath.valid.1 selectedParentless selectedPath normal
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat normalKind canonical.component := by
    intro index included bounded
    have size : topology.nodes.size = tree.nodes.data.size := by
      unfold topology
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact canonical.permissions normalKind index included (by rw [←size];exact bounded)
  have actual := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections anchor normalKind mode
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
      (tree.performNormalAccessAt location anchor normalKind protections mode).location.perms.get index = location.perms.get index := by
    intro index node present member
    have physicalPath := GeneralBorrowWildcardControlWitness.path_of_walk tree depth other index node present _ member
    have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections other index physicalPath
    apply GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor normalKind mode canonical.component index node present
    intro contained
    rw [canonicalSupport] at contained
    apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology selected.toNat other.toNat index.toNat
      selectedPath.valid.1 otherValid selectedParentless otherParentless _ contained projectedPath
    intro same
    exact different (GeneralBorrowNodeUpdate.index_injective selected other same)
  have slotFrame : ∀ index, support index →
      (tree.performNormalAccessAt location anchor normalKind protections mode).location.perms.get index = location.perms.get index := by
    intro index included
    obtain ⟨node,present⟩ := callback.present index included
    apply componentSlots index node present
    apply callback.covers index included (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)
    simp [GeneralBorrowExposureAncestorFold.walk]
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections other rootPosition maximum callbackKind support callback coherent short
  exact ⟨actual.1,actual.2.1,actual.2.2,slotFrame,
    GeneralBorrowRootLocalCounterFrame.snapshot tree location _ protections other rootPosition maximum callbackKind support snapshot coherent actual.2.2 callback.covers componentSlots slotFrame,componentSlots⟩


/-- Original Snapshot API, preserved as a projection of the framed result. -/
theorem after_normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (normalKind callbackKind : AccessKind) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (callback : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections other rootPosition maximum callbackKind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let after := (tree.performNormalAccessAt location anchor normalKind protections mode).location
    (tree.performNormalAccessAt location anchor normalKind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor normalKind protections mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
    (∀ index, support index → after.perms.get index = location.perms.get index) ∧
    Snapshot tree after protections other rootPosition maximum callbackKind support := by
  obtain ⟨complete,ok,afterCoherent,slots,snapshot,componentSlots⟩ := after_normal_framed tree location protections formed anchor selected other anchorNode anchorPresent normal rootPath otherMember different normalKind callbackKind rootPosition maximum support callback coherent short mode
  exact ⟨complete,ok,afterCoherent,slots,snapshot⟩

/-- Actual normal Read OR Write transports full residual authorization of
an untouched other physical-root component, for ANY callback kind/cutoff.
All current legal masks are internally filtered by the generic data theorem;
no empty-mask, tag-order, separation or operation-success premise is added. -/
theorem after_normal_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (normalKind callbackKind : AccessKind) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (callback : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections other rootPosition maximum callbackKind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let after := (tree.performNormalAccessAt location anchor normalKind protections mode).location
    (tree.performNormalAccessAt location anchor normalKind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor normalKind protections mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
    (∀ index, support index → after.perms.get index = location.perms.get index) ∧
    Snapshot tree after protections other rootPosition maximum callbackKind support ∧
    DuplicatePrefixResidualSupportAuthorization.Authorization tree after protections other rootPosition maximum callbackKind support := by
  obtain ⟨complete,ok,afterCoherent,slots,snapshot,componentSlots⟩ := after_normal_framed tree location protections formed anchor selected other anchorNode anchorPresent normal rootPath otherMember different normalKind callbackKind rootPosition maximum support callback coherent short mode
  exact ⟨complete,ok,afterCoherent,slots,snapshot,
    GeneralBorrowRootLocalAuthorization.authorization tree location _ protections other rootPosition maximum callbackKind support callback componentSlots⟩
end DuplicatePrefix.GeneralBorrowNormalOtherRootSnapshot
