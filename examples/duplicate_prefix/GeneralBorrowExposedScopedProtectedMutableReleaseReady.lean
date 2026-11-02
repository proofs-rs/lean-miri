import duplicate_prefix.GeneralBorrowExposedScopedAsMutReleaseReady
import duplicate_prefix.GeneralBorrowExposedScopedAsMutConstructorReleaseData
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableTagHidden
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReleaseReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildMutable
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual protected constructor, callbacks and singleton helper endCall form
copy-ready data at the exact returned child index and original borrowed slice. -/
theorem ready (input : Input) (global : GlobalState) (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedProtectedMutableLeafConstructor.Resources input global.protectedTags selected head tail)
    (nodeTags : ∀ index node,input.tree.nodeAt index=some node → input.tree.indexOfTag node.tag=some index)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let released := (result input).releaseProtector input.newTag global.protectedTags
    let frame := ({} : FrameState).addProtector allocation input.newTag
    released.status=.Released ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context released.tree (index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location =>
          Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data released.tree location (global.endCall frame).protectedTags
            (index input) selected head tail (fun position => raw.component.support position ∨ position=(index input).toNat) (fun _=>true)) ∧
          Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released.tree location (global.endCall frame).protectedTags
            (index input) selected head tail .Write)) input.offset (input.offset+input.len) released.tree.locations ∧
        released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  let protections := global.protectedTags
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
  let plan : GeneralBorrowExposedScopedAsMutReleasePlan.Input (result input) global.protectedTags input.newTag :=
    ⟨index input,selected,head,tail,context,
      (fun position => raw.component.support position ∨ position=(index input).toNat),input.offset,input.offset+input.len,
      positive,fits,metadata.freshLookup,hidden,geometry.1,activity,owned⟩
  let frame := ({} : FrameState).addProtector allocation input.newTag
  have frameHidden : ∀ row∈frame.protectedTags.toList,∀ query node,(result input).nodeAt query=some node → node.tag=row.2 → node.isExposed=false := by
    intro row member query node present equal
    have same : row=(allocation,input.newTag) := by simpa only [frame,FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_cons,List.mem_nil_iff,or_false] using member
    subst row
    exact GeneralBorrowExposedScopedProtectedMutableTagHidden.hidden input nodeTags query node present equal
  have done := GeneralBorrowExposedScopedAsMutReleaseReady.ready (result input) global frame input.newTag plan frameHidden
  refine ⟨done.1,?_⟩
  obtain ⟨nextContext,nextOwned,well,size⟩ := done.2
  exact ⟨nextContext,nextOwned,well,size.trans geometry.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReleaseReady
