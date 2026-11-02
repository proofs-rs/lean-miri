import duplicate_prefix.GeneralBorrowProtectedLifetimeSeed
import duplicate_prefix.GeneralBorrowRangeSifaConsistency
import duplicate_prefix.GeneralBorrowAllocationSifaConsistency
import duplicate_prefix.GeneralBorrowPositiveConstructorSifaProfile
import duplicate_prefix.GeneralBorrowProtectedReservationType
namespace DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedLifetimeSeed GeneralRangeMapState GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem seed_owned (protections : ProtectedTags) :
    Every (GeneralBorrowRange.LocationOwned initial protections GeneralBorrowFullSharedSeed.root .Read) initial.locations := by
  intro position valid
  have zero : position = 0 := by change position < 1 at valid;omega
  subst position
  have topology : (source_normal_projection initial initial.locations.entries[0].data protections).topology = GeneralBorrowFullSharedSeed.normal.topology := by
    unfold_general_projection
    unfold_general_topology
    with_unfolding_all rfl
  refine ⟨⟨by rw [topology];exact GeneralBorrowFullSharedSeed.normalForest⟩,?_⟩
  refine {anchorValid := by rw [topology];decide,locationsAligned := ?_,defaultsAligned := ?_,permissions := ?_}
  · rw [(projection_sizes initial _ protections).1,topology];rfl
  · rw [(projection_sizes initial _ protections).2,topology];rfl
  · intro index bounded
    have zero : index = 0 := by rw [topology] at bounded;change index < 1 at bounded;omega
    subst index
    refine ⟨GeneralBorrowWildcardLeaf.unique,rfl,?_⟩
    have localRel : GeneralBorrowAnchor.relation (source_normal_projection initial initial.locations.entries[0].data protections)
        GeneralBorrowFullSharedSeed.root.toNat 0 = .LocalAccess := by
      unfold GeneralBorrowAnchor.relation
      rw [topology]
      decide +kernel
    have held : (source_normal_projection initial initial.locations.entries[0].data protections).protectedNodes.contains 0 = protections.contains BorTag.one :=
      GeneralBorrowNormalPermissionMetadata.held initial _ protections GeneralBorrowFullSharedSeed.root input.parentNode input.parentPresent
    rw [localRel,held]
    simp [GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.LocalReadable,GeneralBorrowWildcardLeaf.unique,LocationState.possible,Permission.isUnique]

/-- The actual initial root Read forms the complete physical permission/SIFA
profile for every protection table, directly from BorrowTree.new. -/
theorem seed_read_profile (protections : ProtectedTags) :
    Every (fun location => GeneralBorrowLocationSifaConsistency.Profile
      (GeneralBorrowProtectedReadableStage.read input protections).tree location protections)
      (GeneralBorrowProtectedReadableStage.read input protections).tree.locations := by
  have accessed := GeneralBorrowRangeSifaConsistency.ranged initial protections BorTag.one GeneralBorrowFullSharedSeed.root GeneralBorrowFullSharedSeed.root
    (Size.ofBytes 0) (Size.ofBytes 1) .Read .VisitChildrenOfAccessed (by decide) input.depth input.children input.parentNode input.parentPresent
    rfl input.covered input.parentTagPresent input.well (GeneralBorrowAllocationSifaConsistency.allocation 1 BorTag.one protections)
    0 1 (by intro position valid positive low high;exact seed_owned protections position valid) (Nat.le_refl _) (by decide) input.bounds
  exact accessed.2.1

/-- The actual first protected constructor forms both the scalar SIFA profile
and its new reservation's physical typing. Permission-Clean is derived from
the source Read profile's vacant-node invariant, rather than assumed. -/
theorem first_constructor_profile (protections : ProtectedTags)
    (prepared : GeneralBorrowProtectedReadableStage.Prepared input protections)
    (held : protections.contains tag2 = true) :
    Every (fun location => GeneralBorrowLocationSifaConsistency.Profile
      (GeneralBorrowFreshMetadataChildMutable.result prepared.next) location protections)
      (GeneralBorrowFreshMetadataChildMutable.result prepared.next).locations ∧
    GeneralBorrowDefaultReservationType.TreeTyped (GeneralBorrowFreshMetadataChildMutable.result prepared.next)
      (GeneralBorrowFreshMetadataChildMutable.index prepared.next) := by
  have readProfile : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile prepared.next.tree location protections)
      prepared.next.tree.locations := by
    rw [prepared.tree]
    exact seed_read_profile protections
  have vacancy : prepared.next.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index prepared.next) = none := by
    unfold UniValMap.get
    rw [GeneralBorrowFreshMetadataChildMutable.at_end prepared.next]
    rw [Array.getElem?_eq_none (Nat.le_refl _)]
  have clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index prepared.next) = none) prepared.next.tree.locations :=
    fun position valid => (readProfile position valid).vacant _ vacancy
  exact ⟨(GeneralBorrowPositiveConstructorSifaProfile.Protected.append prepared.next protections
    (by rw [prepared.tag];exact held) readProfile).2,GeneralBorrowProtectedReservationType.Append.formed prepared.next clean⟩
end DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoSeed
