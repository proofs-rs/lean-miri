import duplicate_prefix.GeneralBorrowFreshReleaseMixed
import duplicate_prefix.GeneralBorrowFreshSharedAnchor
namespace DuplicatePrefix.GeneralBorrowFreshMixedChild
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshMaterialization
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

def extend (writable : Nat → Bool) (index : Nat) : Nat → Bool :=
  fun position => if position = index then false else writable position

/-- The exact parent Write contract supplies initial all-writable mixed data.
No stronger property is inferred from mere child Read ownership. -/
theorem write_combined (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (anchor : UniIndex)
    (owned : GeneralBorrowRange.LocationOwned tree protections anchor .Write location) :
    Combined tree protections anchor (fun _ => true) location := by
  obtain ⟨forest,owner⟩ := owned
  refine ⟨⟨forest,GeneralBorrowFreshAnchor.anchor_readable _ anchor.toNat owner⟩,?_⟩
  intro position valid
  obtain ⟨state,present,permitted⟩ := owner.permissions position (by rw [←owner.locationsAligned];exact valid)
  exact ⟨state,present,permitted⟩

private theorem mixed_extension (before after : NormalTreeState) (parent child : Nat) (writable : Nat → Bool)
    (old : GeneralBorrowOwnership.Pointwise before writable (GeneralBorrowAnchor.relation before parent))
    (oldPosition : ∀ position, position < after.locationStates.size → position ≠ child → position < before.locationStates.size)
    (states : ∀ position, position < before.locationStates.size → position ≠ child → after.stateAt position = before.stateAt position)
    (protections : ∀ position, position < before.locationStates.size → position ≠ child → after.protectedNodes.contains position = before.protectedNodes.contains position)
    (path : after.topology.ancestorPath child = child :: before.topology.ancestorPath parent)
    (newState : after.stateAt child = some GeneralBorrowFreshAnchor.sharedState) :
    GeneralBorrowOwnership.Pointwise after (extend writable child) (GeneralBorrowAnchor.relation after child) := by
  intro position valid
  by_cases fresh : position = child
  · subst position
    refine ⟨GeneralBorrowFreshAnchor.sharedState,newState,?_⟩
    simp only [extend,ite_true]
    change GeneralBorrowPermissions.Required _ false (GeneralBorrowAnchor.relation after child child) _
    have localRelation : GeneralBorrowAnchor.relation after child child = .LocalAccess := by
      unfold GeneralBorrowAnchor.relation
      rw [path]
      simp
    rw [localRelation]
    exact GeneralBorrowPermissions.fresh_shared_readable .Read true
  · have oldValid := oldPosition position valid fresh
    obtain ⟨state,present,permitted⟩ := old position oldValid
    refine ⟨state,(states position oldValid fresh).trans present,?_⟩
    have related : GeneralBorrowAnchor.relation after child position = GeneralBorrowAnchor.relation before parent position := by
      unfold GeneralBorrowAnchor.relation
      rw [path]
      simp only [List.mem_cons,fresh,false_or]
    simpa only [extend,fresh,↓reduceIte,related,protections position oldValid fresh] using permitted

/-- Actual append node/per-location insertion preserves every previous label
and gives only the new Frozen child a read-only label. -/
theorem append_location (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : Combined tree protections parent writable location) :
    Combined (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent))
      protections index (extend writable index.toNat) (materialized location index GeneralBorrowFreshAnchor.sharedState) := by
  let next := GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
  let nextLocation := materialized location index GeneralBorrowFreshAnchor.sharedState
  have newOwned := GeneralBorrowFreshAnchor.shared_location_owned tree index parent parentNode tag atEnd parentPresent location protections owned.1
  refine ⟨newOwned,?_⟩
  obtain ⟨⟨forest⟩,owner⟩ := owned.1
  have extension := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
    atEnd parentPresent rfl rfl location nextLocation protections
  have beforeSizes := GeneralBorrowProjection.projection_sizes tree location protections
  have nextSizes := GeneralBorrowProjection.projection_sizes next nextLocation protections
  have topologySize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size :=
    owner.locationsAligned.symm.trans beforeSizes.1
  have afterSize : (source_normal_projection next nextLocation protections).locationStates.size = tree.nodes.data.size+1 := by
    rw [newOwned.2.locationsAligned,extension.length,topologySize]
  apply mixed_extension (source_normal_projection tree location protections)
    (source_normal_projection next nextLocation protections) parent.toNat index.toNat writable owned.2
  · intro position valid different
    rw [afterSize] at valid
    rw [beforeSizes.1]
    omega
  · intro position valid different
    have bounded : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshMaterialization.state_old tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      atEnd parentPresent location GeneralBorrowFreshAnchor.sharedState protections position bounded
  · intro position valid different
    have bounded : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshMaterialization.protection_old tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      atEnd parentPresent location nextLocation protections position bounded
  · exact GeneralBorrowFreshProjection.projected_ancestors tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      atEnd parentPresent rfl rfl location nextLocation protections forest
  · exact GeneralBorrowFreshMaterialization.state_new tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      atEnd parentPresent location GeneralBorrowFreshAnchor.sharedState protections

/-- Bounded vacant-slot reuse has the same mixed-label extension, even if
stale per-location permissions existed at that slot before inside overwrite. -/
theorem reuse_location (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : Combined tree protections parent writable location) :
    Combined (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent))
      protections index (extend writable index.toNat) (materialized location index GeneralBorrowFreshAnchor.sharedState) := by
  let next := GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
  let nextLocation := materialized location index GeneralBorrowFreshAnchor.sharedState
  have newOwned := GeneralBorrowFreshSharedAnchor.reuse_location_owned tree index parent parentNode tag bounded vacant fits parentPresent location protections owned.1
  refine ⟨newOwned,?_⟩
  obtain ⟨⟨forest⟩,owner⟩ := owned.1
  have beforeSizes := GeneralBorrowProjection.projection_sizes tree location protections
  have nextSizes := GeneralBorrowProjection.projection_sizes next nextLocation protections
  have afterSize : (source_normal_projection next nextLocation protections).locationStates.size = tree.nodes.data.size := by
    rw [nextSizes.1,GeneralBorrowFreshReuseState.attached_size tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      bounded vacant parentPresent]
  apply mixed_extension (source_normal_projection tree location protections)
    (source_normal_projection next nextLocation protections) parent.toNat index.toNat writable owned.2
  · intro position valid different
    rw [beforeSizes.1]
    rw [afterSize] at valid
    exact valid
  · intro position valid different
    have validOld : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshReuseState.state_old tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      bounded vacant parentPresent fits location GeneralBorrowFreshAnchor.sharedState protections position validOld different
  · intro position valid different
    have validOld : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      vacant parentPresent location nextLocation protections fits position validOld different
  · exact GeneralBorrowFreshReuseProjection.projected_ancestors tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      bounded vacant parentPresent rfl rfl location nextLocation protections forest
  · exact GeneralBorrowFreshReuseState.state_new tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)
      bounded vacant parentPresent location GeneralBorrowFreshAnchor.sharedState protections
end DuplicatePrefix.GeneralBorrowFreshMixedChild
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedChild.append_location
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedChild.reuse_location

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMixedChild." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mixed shared construction dependency {dependency}"
