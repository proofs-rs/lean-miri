import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableProtectedMutableReadReleaseReady
import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableArgumentRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAsMutRawReady
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial raw caller resources derive the release contract of the real
registered protected mutable FnEntry result. No successful retag or final
release/ownership proposition is accepted as an input. -/
theorem ready (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId) (parentTag : BorTag) (offset len : UInt64)
    (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedWritableMutableEntryRaw.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail)
    (positive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index data.input)=none) data.input.tree.locations) :
    let held := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
    let child := GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree tree tracker parentTag offset len
    let released := child.releaseProtector tracker.global.nextPointerTag held.protectedTags
    let frame := ({} : FrameState).addProtector allocation tracker.global.nextPointerTag
    released.status=.Released ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context released.tree (GeneralBorrowFreshMetadataChildMutable.index data.input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location =>
          Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released.tree location (held.endCall frame).protectedTags
            (GeneralBorrowFreshMetadataChildMutable.index data.input) selected head tail
            (fun position => data.resources.component.support position ∨ position=(GeneralBorrowFreshMetadataChildMutable.index data.input).toNat) (fun _=>true)) ∧
          Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released.tree location (held.endCall frame).protectedTags
            (GeneralBorrowFreshMetadataChildMutable.index data.input) selected head tail .Write)) offset (offset+len) released.tree.locations ∧
        released.tree.locations.WellFormed ∧ released.tree.locations.size=tree.locations.size := by
  have absentInput : data.input.tree.indexOfTag data.input.newTag=none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find data.input.tree.tagMapping data.input.newTag data.input.fresh,Option.map_none]
  have absent : data.input.tree.indexOfTag tracker.global.nextPointerTag=none := by
    simpa only [data.newTagEq] using absentInput
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedWritableProtectedMutableProtect.protect data.input tracker.global.protectedTags tracker.global.nextPointerTag
    selected head tail data.resources (by
      intro index node present equal
      have mapped : data.input.tree.indexOfTag node.tag=some index := by
        rw [data.treeEq] at present ⊢
        exact data.nodeTags index node present
      rw [equal,absent] at mapped
      cases mapped)
  have result := GeneralBorrowExposedScopedWindowWritableProtectedMutableReadReleaseReady.ready data.input
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag) allocation selected head tail
    held
    (by intro index node present;rw [data.treeEq] at present ⊢;exact data.nodeTags index node present) positive clean
  dsimp only at result
  have childEq : ((data.input.tree.performBorrowAccessRange (.concrete data.input.parentTag) (Size.ofBytes data.input.offset)
      (Size.ofBytes data.input.len) .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes data.input.offset) (.concrete data.input.parentTag) data.input.newTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes data.input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree =
      GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree tree tracker parentTag offset len := by
    simp only [GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree,data.treeEq,data.parentTagEq,data.newTagEq,data.offsetEq,data.lenEq]
  rw [childEq,data.newTagEq] at result
  simpa only [support,data.treeEq,data.newTagEq,data.offsetEq,data.lenEq] using result
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAsMutRawReady
