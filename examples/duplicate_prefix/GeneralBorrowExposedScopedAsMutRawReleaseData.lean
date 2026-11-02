import duplicate_prefix.GeneralBorrowExposedScopedAsMutEntryReleaseData
import duplicate_prefix.GeneralBorrowExposedScopedMutableArgumentRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedAsMutRawReleaseData
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial raw caller resources derive the release contract of the real
registered protected mutable FnEntry result. No successful retag or final
release/ownership proposition is accepted as an input. -/
noncomputable def build (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64)
    (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedMutableEntryRaw.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail)
    (atBase : data.input.offset=0) (full : data.input.len=data.input.tree.locations.size.bytes)
    (positive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildDefault.index data.input)=none) data.input.tree.locations) :
    GeneralBorrowExposedScopedAsMutReleasePlan.Input
      (GeneralBorrowExposedScopedMutableArgumentRaw.finalTree tree tracker parentTag offset len)
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags tracker.global.nextPointerTag := by
  apply Classical.choice
  have absent : data.input.tree.indexOfTag data.input.newTag=none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find data.input.tree.tagMapping data.input.newTag data.input.fresh,Option.map_none]
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedDefaultLeafProtect.protect data.input tracker.global.protectedTags data.input.newTag
    selected head tail data.resources (by
      intro index node present equal
      have mapped : data.input.tree.indexOfTag node.tag=some index := by
        rw [data.treeEq] at present ⊢
        exact data.nodeTags index node present
      rw [equal,absent] at mapped
      cases mapped)
  let result := GeneralBorrowExposedScopedAsMutEntryReleaseData.build data.input
    (tracker.global.protectedTags.insert data.input.newTag .StrongProtector) selected head tail held atBase full positive clean
  refine ⟨?_⟩
  simpa only [GeneralBorrowExposedScopedMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,
    data.treeEq,data.parentTagEq,data.newTagEq,data.offsetEq,data.lenEq] using result
end DuplicatePrefix.GeneralBorrowExposedScopedAsMutRawReleaseData
