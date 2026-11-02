import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAsMutEntryReleaseData
import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableArgumentRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAsMutRawReleaseData
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial raw mixed writable-leaf data derive the real protected FnEntry's
release input, without any retag/release success or final ownership premise. -/
noncomputable def build (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64)
    (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedWritableMutableEntryRaw.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail)
    (positive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index data.input)=none) data.input.tree.locations) :
    GeneralBorrowExposedScopedWritableAsMutReleasePlan.Input
      (GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree tree tracker parentTag offset len)
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags tracker.global.nextPointerTag := by
  apply Classical.choice
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedWritableMutableEntryInput.register data.input tracker.global.protectedTags
    selected head tail data.resources (by simpa only [data.treeEq] using data.nodeTags)
  let result := GeneralBorrowExposedScopedWindowWritableAsMutEntryReleaseData.build data.input
    (tracker.global.protectedTags.insert data.input.newTag .StrongProtector) selected head tail held positive clean
  refine ⟨?_⟩
  simpa only [GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,
    data.treeEq,data.parentTagEq,data.newTagEq,data.offsetEq,data.lenEq] using result
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAsMutRawReleaseData
