import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableLeafReadConstructor
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableActivity
import duplicate_prefix.GeneralBorrowFreshMutableGeometry
import duplicate_prefix.GeneralBorrowExposedScopedAsMutReleasePlan
namespace DuplicatePrefix.GeneralBorrowExposedScopedAsMutConstructorReleaseData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildMutable
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- A freshly constructed protected reservation has a genuine data-only pop
plan input. Activity and every callback resource come from the real constructor. -/
noncomputable def build (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedProtectedMutableLeafConstructor.Resources input protections selected head tail)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    GeneralBorrowExposedScopedAsMutReleasePlan.Input (result input) protections input.newTag := by
  apply Classical.choice
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedProtectedMutableLeafReadConstructor.construct_unique input protections selected head tail raw
  let metadata := GeneralBorrowFreshMetadataChildMutable.append input
  have geometry := GeneralBorrowFreshMutableGeometry.append_frame input
  have activity := GeneralBorrowExposedScopedProtectedMutableActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.offset input.len input.nonzero
    input.well input.bounds clean
  have fits : (result input).nodes.data.size≤4294967296 := by
    change (result input).nodes.size≤4294967296
    rw [metadata.size]
    have room:=raw.room
    omega
  have hidden : context.anchorNode.isExposed=false := by
    obtain ⟨node,present,tag,parent,children,permission,exposed⟩ := metadata.newNode
    have same := Option.some.inj (context.anchorPresent.symm.trans present)
    rw [same]
    exact exposed
  exact ⟨⟨index input,selected,head,tail,context,
    (fun position => raw.component.support position ∨ position=(index input).toNat),input.offset,input.offset+input.len,
    positive,fits,metadata.freshLookup,hidden,geometry.1,activity,owned⟩⟩
end DuplicatePrefix.GeneralBorrowExposedScopedAsMutConstructorReleaseData
