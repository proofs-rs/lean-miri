import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultNext
import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultData
import duplicate_prefix.GeneralBorrowExposedScopedDefaultConstructorAllocator
import duplicate_prefix.GeneralBorrowExposedScopedWritableCleanReadRange
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultNextAllocator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual expression parent Read and Default append retain graph-tag lookup
and all vacant-slot cleanliness. No post-constructor allocator data are inputs. -/
theorem preserves (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes) (mode : ChildrenVisitMode)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) (clean : GeneralBorrowGcVacantClean.VacantClean input.tree) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    GeneralBorrowGcAllocator.NodeTags child.tree ∧ GeneralBorrowGcVacantClean.VacantClean child.tree := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedWritableDefaultRun.prepare input protections selected head tail raw atBase full mode
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
  have preparedTags : GeneralBorrowGcAllocator.NodeTags prepared.tree := by
    intro query node present
    rw [treeEq,frame] at present ⊢
    exact nodeTags query node present
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedWritableDefaultData.build input protections selected head tail raw
  have fits : input.tree.nodes.data.size≤4294967296 := by have a:=input.aligned;have b:=input.fits;omega
  have preparedClean : GeneralBorrowGcVacantClean.VacantClean prepared.tree := by
    intro query vacant
    have oldVacant : input.tree.nodes.get query=none := by rw [treeEq,frame] at vacant;exact vacant
    have good := GeneralBorrowExposedScopedWritableCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head query tail
      (Size.ofBytes input.offset) (Size.ofBytes input.len) mode context raw.component.support (fun _=>true) fits
      input.parentTagPresent oldVacant (clean query oldVacant) input.well input.offset (input.offset+input.len) owned input.bounds
      (Nat.le_refl _) (Nat.le_refl _)
    rw [treeEq]
    exact good.2
  have tags := GeneralBorrowExposedScopedDefaultConstructorAllocator.nodeTags prepared preparedTags
  have vacant := GeneralBorrowExposedScopedDefaultConstructorAllocator.clean prepared preparedClean
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  rw [childEq] at tags vacant
  exact ⟨tags,vacant⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultNextAllocator
