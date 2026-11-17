import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafConstructor
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowExposedScopedUniqueRelease
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafReleaseUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Real shared child formation and its real protector-end callbacks are joined
from initial resources and a clean allocator slot. Activity, child contracts,
release success and final partition geometry are all derived. -/
theorem release (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    let child := result input
    let released := child.releaseProtector input.newTag protections
    released.status = .Released ∧ released.tree = {child with locations := released.tree.locations} ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data released.tree location protections
        (index input) selected head tail (fun position => raw.component.support position ∨ position = (index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)))
        input.offset (input.offset+input.len) released.tree.locations ∧
      released.tree.locations.WellFormed ∧ released.tree.locations.size = input.tree.locations.size := by
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  let child := result input
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedSharedLeafConstructor.construct input protections selected head tail writable raw
  have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
  have activity := GeneralBorrowExposedScopedSharedActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len
    input.nonzero input.well input.bounds clean
  have active := GeneralBorrowFreshActiveWithin.active_on child (index input) .Read input.offset (input.offset+input.len) geometry.1 activity
  have fits : child.nodes.data.size ≤ 4294967296 := by
    change child.nodes.size ≤ 4294967296
    rw [metadata.size]
    have bound := raw.room
    omega
  have hidden : context.anchorNode.isExposed = false := by
    obtain ⟨node,present,tag,parent,children,permission,exposed⟩ := metadata.newNode
    have same := Option.some.inj (context.anchorPresent.symm.trans present)
    rw [same]
    exact exposed
  have childShort : child.nodes.size<65536 := by rw [metadata.size];exact raw.room
  have childLeaves : ∀ query,area.support query → ∃ node,child.nodeAt query=some node ∧ node.children=#[] ∧ node.isExposed=true := by
    intro query included
    obtain ⟨old,present,leaf,exposed⟩ := raw.leaves query included
    have different : query≠input.parent := by
      intro same
      have separate:=raw.separate query included
      apply separate
      rw [same]
      exact raw.component.anchor
    obtain ⟨node,found,tag,parent,children,permission,exposure⟩ := GeneralBorrowExposedScopedSharedOld.outside_parent input query old present different
    exact ⟨node,found,children.trans leaf,exposure.trans exposed⟩
  have childUnique : ∀ query,area.support query → GeneralBorrowSifaUniqueFrame.UniqueAt child query := by
    intro query included
    obtain ⟨old,present,leaf,exposed⟩ := raw.leaves query included
    exact GeneralBorrowExposedScopedSharedOld.unique input query old present (raw.unique query included)
  have uniqueOwned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data child location protections (index input) selected head tail
        (fun position => raw.component.support position ∨ position=(index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (index input).toNat))) input.offset (input.offset+input.len) child.locations := by
    intro position valid positive lower upper
    obtain ⟨base⟩ := owned position valid positive lower upper
    exact ⟨{base:=base,short:=childShort,leaves:=childLeaves,unique:=fun query included=>childUnique query included position valid}⟩
  have done := GeneralBorrowExposedScopedUniqueRelease.release child protections input.newTag (index input) selected head tail context
    (fun position => raw.component.support position ∨ position = (index input).toNat)
    (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) input.offset (input.offset+input.len) positive fits hidden
    metadata.freshLookup active uniqueOwned
  have releasedGeometry := GeneralBorrowStructuralReleaseGeometry.release child protections input.newTag geometry.1
  exact ⟨done.1,done.2.1,done.2.2,releasedGeometry.1,releasedGeometry.2.trans geometry.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafReleaseUnique
