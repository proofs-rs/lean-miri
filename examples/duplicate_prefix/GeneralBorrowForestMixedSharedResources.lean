import duplicate_prefix.GeneralBorrowForestMixedSharedVacantClean
import duplicate_prefix.GeneralBorrowForestForeignSharedFresh
import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Next (tree : BorrowTree) (protections : ProtectedTags) (newTag nextTag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (writable : Nat → Bool) where
  context : Context tree anchor primary extras
  covered : GeneralBorrowGraph.RootsCover tree
  allocator : GeneralBorrowGcAllocator.Invariant tree
  well : tree.locations.WellFormed
  bound : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  tag : tree.indexOfTag newTag = some anchor
  nextFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag
  slot : Slot tree context.depth anchor
  clean : GeneralRangeMapState.Every
    (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) tree.locations
  nodeFits : tree.nodes.data.size ≤ 4294967296
  owned : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections anchor primary extras writable))
    offset (offset+len) tree.locations

/-- The actual unprotected shared expression forms all graph, mixed ownership,
next fresh key, allocator-selected slot and permission cleanliness needed by
shared FnEntry. Only initial metadata/resources and two distinct unused tags
are supplied; no next-input or operation-success outcome is assumed. -/
def build (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag nextTag : BorTag)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (writable : Nat → Bool) (allocator : GeneralBorrowGcAllocator.Invariant tree)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections parent primary extras writable))
      offset (offset+len) tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag) (different : newTag ≠ nextTag)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    let after := (GeneralBorrowForestMixedShared.child tree protections parentTag newTag false offset len .VisitChildrenOfAccessed).tree
    Next after protections newTag nextTag (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras offset len
      (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat) := by
  have foreign : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestForeignAccess.LocationData tree location protections parent primary extras .Read))
      offset (offset+len) tree.locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := before position valid positive start stop
    exact ⟨data.base⟩
  have result := GeneralBorrowForestMixedShared.run tree protections parentTag newTag false parent primary extras offset len
    .VisitChildrenOfAccessed context covered parentTagPresent fresh slot fits writable nonzero well bounds before
  have resources := GeneralBorrowForestForeignSharedResources.preserves tree protections parentTag newTag false parent primary extras offset len
    .VisitChildrenOfAccessed context covered parentTagPresent fresh slot fits nonzero well bounds allocator foreign
  have future := GeneralBorrowForestForeignSharedFresh.preserves tree protections parentTag newTag false parent primary extras offset len
    .VisitChildrenOfAccessed context covered parentTagPresent fresh slot fits nonzero well bounds foreign nextTag futureFresh different
  have vacant := GeneralBorrowForestMixedSharedVacantClean.preserves tree protections parentTag newTag false parent primary extras offset len
    .VisitChildrenOfAccessed context covered parentTagPresent fresh slot fits nonzero well bounds writable allocator before clean
  let after := (GeneralBorrowForestMixedShared.child tree protections parentTag newTag false offset len .VisitChildrenOfAccessed).tree
  let anchor := GeneralBorrowFreshMetadataChildSlot.index slot
  change GeneralBorrowGcAllocator.Invariant after ∧ after.locations.WellFormed ∧
    after.locations.size = tree.locations.size ∧ after.nodes.size ≤ tree.nodes.size+1 ∧
    GeneralBorrowGraph.RootsCover after ∧ after.indexOfTag newTag = some anchor at resources
  let nextContext := Classical.choice result.2.2.1
  let depth := GeneralBorrowCanonicalParentDepth.normalize after.nodes nextContext.depth
  let normalized : Context after anchor primary extras := {nextContext with depth := depth}
  have nextRoom : after.nodes.size+4 ≤ 4294967295 := by have size := resources.2.2.2.1;omega
  have aligned := GeneralBorrowFreshStagePool.empty_aligned after resources.1.accounting
  have mappingFits : after.tagMapping.deassigned.back? = none → after.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    change after.nodes.data.size+4 ≤ _ at nextRoom
    omega
  let nextSlot := GeneralBorrowCanonicalParentDepth.slot after nextContext.depth anchor nextContext.anchorNode nextContext.anchorPresent
    resources.1.pool aligned mappingFits
  exact {
    context := normalized,covered := resources.2.2.2.2.1,allocator := resources.1,well := resources.2.1,
    bound := by change offset.toNat+len.toNat ≤ after.locations.size.bytes.toNat;rw [resources.2.2.1];exact bounds,
    tag := resources.2.2.2.2.2,nextFresh := future,slot := nextSlot,
    clean := vacant _ (GeneralBorrowFreshSharedWithinStages.slot_vacant after depth anchor nextSlot),
    nodeFits := by change after.nodes.data.size ≤ 4294967296;change after.nodes.data.size+4 ≤ _ at nextRoom;omega,
    owned := result.2.2.2 }
end
end DuplicatePrefix.GeneralBorrowForestMixedSharedResources
