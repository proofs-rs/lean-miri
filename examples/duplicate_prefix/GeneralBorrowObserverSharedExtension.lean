import duplicate_prefix.GeneralBorrowSharedMaterializedNormal
import duplicate_prefix.GeneralBorrowSharedMaterializedCapability

namespace DuplicatePrefix.GeneralBorrowObserverSharedExtension
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowFreshNormalComponent GeneralBorrowSharedNormalTables
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Any existing observer component, containing the actual constructor parent,
extends across the fresh shared leaf. This does not identify the observer with
the constructor parent or require source Write permission. -/
def component (before after : TraversalTree) (parent child observer : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before observer)
    (supported : old.support parent) (patch : Patch before after parent child) :
    GeneralBorrowExposedScopedNormal.Component after observer where
  support := extended old.support child
  anchor := .inr old.anchor
  parents := by
    intro current included parentNode edge
    by_cases fresh : current = child
    · subst current
      rw [patch.leaf] at edge
      have same : parent = parentNode := Option.some.inj edge
      rw [←same]
      exact .inr supported
    · exact .inr (old.parents current (included.resolve_left fresh) parentNode
        ((patch.oldParents current fresh).symm.trans edge))
  children := by
    intro current included query member
    by_cases fresh : current = child
    · subst current
      rw [patch.leaf] at member
      cases member
    · rcases patch.oldChildren current fresh query member with newChild | oldChild
      · exact .inl newChild
      · exact .inr (old.children current (included.resolve_left fresh) query oldChild)

/-- Virtual unprotection of the new child preserves any old mutable observer's
Both table through actual shared materialization. All supplied data concern the
initial graph or exact finite node update; no access completion is assumed. -/
theorem tables (before after : NormalTreeState) (parent child observer : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology observer)
    (supported : old.support parent)
    (extension : Extension before after parent child)
    (valid : observer < before.topology.nodes.size) (different : observer ≠ child)
    (permissions : ∀ kind,Table before observer kind old.support) :
    ∀ kind,Table after observer kind (component before.topology after.topology parent child observer old supported extension.patch).support := by
  intro kind index included bounded
  by_cases fresh : index = child
  · subst index
    refine ⟨GeneralBorrowFreshAnchor.sharedState,extension.newState,?_⟩
    rw [GeneralBorrowSharedNormalRelations.original_child_foreign before after parent child observer extension.paths valid different,
      extension.freshUnprotected]
    exact DuplicatePrefixConstructorNormalShape.shared_foreign_both kind
  · have oldValid := extension.oldValid index bounded fresh
    obtain ⟨state,present,compatible⟩ := permissions kind index (included.resolve_left fresh) oldValid
    refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
    rw [GeneralBorrowSharedNormalRelations.original before after parent child observer index extension.paths valid different,
      extension.oldProtected index oldValid fresh]
    exact compatible

theorem from_extension (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (parent child observer : UniIndex)
    (normal : DuplicatePrefixBorrowAuthorization.Normal before oldLocation protections observer)
    (supported : normal.component.support parent.toNat)
    (extension : Extension (source_normal_projection before oldLocation protections)
      (source_normal_projection after newLocation protections) parent.toNat child.toNat)
    (valid : observer.toNat < before.nodes.data.size) (different : observer ≠ child) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal after newLocation protections observer,
      next.component.support = extended normal.component.support child.toNat := by
  have beforeSize : (source_normal_projection before oldLocation protections).topology.nodes.size = before.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have afterSize : (source_normal_projection after newLocation protections).topology.nodes.size = after.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have differentNat : observer.toNat ≠ child.toNat := by
    intro equal
    apply different
    cases observer with | mk left =>
      cases child with | mk right =>
        congr 1
        exact UInt32.toNat_inj.mp equal
  let next := component (source_normal_projection before oldLocation protections).topology
    (source_normal_projection after newLocation protections).topology parent.toNat child.toNat observer.toNat normal.component supported extension.patch
  refine ⟨⟨next,?_⟩,rfl⟩
  have table := tables (source_normal_projection before oldLocation protections)
    (source_normal_projection after newLocation protections) parent.toNat child.toNat observer.toNat normal.component supported extension
    (by rw [beforeSize];exact valid) differentNat (by
      intro kind index included bounded
      exact normal.permissions kind index included (by rw [←beforeSize];exact bounded))
  intro kind index included bounded
  exact table kind index included (by rw [afterSize];exact bounded)

/-- Actual append materialization preserves an arbitrary same-component
observer under any virtual protector table in which the fresh tag is absent. -/
theorem append (tree : BorrowTree) (index parent observer : UniIndex) (parentNode observerNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (location : LocationTree) (virtual : ProtectedTags) (unprotected : virtual.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location virtual).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location virtual observer)
    (supported : normal.component.support parent.toNat) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent))
      (GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshAnchor.sharedState) virtual observer,
      next.component.support = extended normal.component.support index.toNat := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes observer observerNode observerPresent
  have different : observer ≠ index := by intro same;subst observer;omega
  exact from_extension tree _ location _ virtual parent index observer normal supported
    (GeneralBorrowSharedMaterializedNormal.append tree index parent parentNode tag atEnd present location virtual unprotected forest)
    valid different

/-- The same observer extension for an actual vacant-slot reuse. -/
theorem reuse (tree : BorrowTree) (index parent observer : UniIndex) (parentNode observerNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (location : LocationTree) (virtual : ProtectedTags) (unprotected : virtual.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location virtual).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location virtual observer)
    (supported : normal.component.support parent.toNat) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent))
      (GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshAnchor.sharedState) virtual observer,
      next.component.support = extended normal.component.support index.toNat := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes observer observerNode observerPresent
  have different : observer ≠ index := by
    intro same
    subst observer
    change tree.nodes.get index = some observerNode at observerPresent
    rw [vacant] at observerPresent
    contradiction
  exact from_extension tree _ location _ virtual parent index observer normal supported
    (GeneralBorrowSharedMaterializedNormal.reuse tree index parent parentNode tag bounded vacant fits present location virtual unprotected forest)
    valid different

end DuplicatePrefix.GeneralBorrowObserverSharedExtension
