import duplicate_prefix.GeneralBorrowExposedScopedDefaultOld
import duplicate_prefix.GeneralBorrowExposedScopedWritableReadData
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultOld
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Fresh shared-child installation retains every old supporting leaf's real
effective writable state, including an absent lazy default. -/
theorem stage (input : Input) (protections : ProtectedTags) (support : UniIndex→Prop)
    (present : ∀query,support query→∃node,input.tree.nodeAt query=some node)
    (notParent : ∀query,support query→query≠input.parent)
    (initial : GeneralRangeMapState.Every (fun location=>∀query node,support query→input.tree.nodeAt query=some node→
      GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location query node)
        .LocalAccess (protections.contains node.tag)) input.tree.locations) :
    GeneralRangeMapState.Every (fun location=>∀query node,support query→(GeneralBorrowFreshMetadataChildDefault.stage input).nodeAt query=some node→
      GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location query node)
        .LocalAccess (protections.contains node.tag)) (GeneralBorrowFreshMetadataChildDefault.stage input).locations := by
  have notNew (query : UniIndex) (included : support query) : query≠index input := by
    obtain ⟨node,found⟩:=present query included
    have bound:=GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes query node found
    intro same
    rw [same,at_end input] at bound
    omega
  have lookup (query : UniIndex) (included : support query) :
      (GeneralBorrowFreshMetadataChildDefault.stage input).nodeAt query=input.tree.nodeAt query := by
    exact GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent query input.parentNode
      (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) (at_end input) input.parentPresent
      (notParent query included) (notNew query included)
  have modified:=GeneralBorrowExposureChildAttach.modify_every
    (fun location=>∀query node,support query→input.tree.nodeAt query=some node→
      GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location query node)
        .LocalAccess (protections.contains node.tag)) input.tree.locations (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location=>GeneralBorrowFreshMaterialization.materialized location (index input) GeneralBorrowFreshDefaultChild.inside)
    input.well input.bounds initial (by
      intro range location good query node included found
      simpa only [GeneralBorrowFreshMaterialization.materialized,GeneralBorrowWildcardVirtualLeaf.effective,
        GeneralBorrowFreshLocation.get_other _ (index input) query _ (notNew query included)] using good query node included found)
  intro position valid query node included found
  rw [lookup query included] at found
  exact modified position valid query node included found
end DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultOld
