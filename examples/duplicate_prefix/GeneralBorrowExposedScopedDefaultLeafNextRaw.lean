import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafNextAllocator
import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafNextGeometry
import duplicate_prefix.GeneralBorrowExposedScopedDefaultExpression
import duplicate_prefix.GeneralBorrowExposedScopedMutableEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafNextRaw
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial raw mutable-expression resources yield initial raw helper FnEntry
resources on the exact physical expression tree. Future-tag freshness, all
vacant-slot hygiene and helper-slot Clean are transported internally. -/
theorem next (tree : BorrowTree) (protections : ProtectedTags) (parentTag exprTag future : BorTag) (offset len : UInt64)
    (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedMutableEntryRaw.Data tree protections parentTag exprTag offset len selected head tail)
    (atBase : data.input.offset=0) (full : data.input.len=data.input.tree.locations.size.bytes)
    (positive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping future) (different : exprTag≠future)
    (room : tree.nodes.size+2<65536) (vacantClean : GeneralBorrowGcVacantClean.VacantClean tree) :
    let child := GeneralBorrowExposedScopedDefaultExpression.child tree protections parentTag exprTag offset len .VisitChildrenOfAccessed
    ∃ next : GeneralBorrowExposedScopedMutableEntryRaw.Data child.tree protections exprTag future offset len selected head tail,
      next.input.parent=index data.input ∧ next.input.offset=0 ∧ next.input.len=next.input.tree.locations.size.bytes ∧
      GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index next.input)=none) next.input.tree.locations := by
  obtain ⟨done,nextInput,nextTree,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,raw,supportEq⟩ :=
    GeneralBorrowExposedScopedDefaultLeafNext.next data.input protections selected head tail data.resources atBase full positive .VisitChildrenOfAccessed
      future (by simpa only [data.treeEq] using futureFresh) (by simpa only [data.newTagEq] using different)
      (by simpa only [data.treeEq] using room)
  have metadata := GeneralBorrowExposedScopedDefaultLeafNextAllocator.preserves data.input protections selected head tail data.resources
    atBase full .VisitChildrenOfAccessed (by simpa only [data.treeEq,GeneralBorrowGcAllocator.NodeTags,BorrowTree.indexOfTag,BorrowTree.nodeAt] using data.nodeTags) (by simpa only [data.treeEq] using vacantClean)
  have geometry := GeneralBorrowExposedScopedDefaultLeafNextGeometry.frame data.input protections selected head tail data.resources atBase full .VisitChildrenOfAccessed
  let child := GeneralBorrowExposedScopedDefaultExpression.child tree protections parentTag exprTag offset len .VisitChildrenOfAccessed
  have childEq : ((data.input.tree.performBorrowAccessRange (.concrete data.input.parentTag) (Size.ofBytes data.input.offset) (Size.ofBytes data.input.len)
      .Read protections .VisitChildrenOfAccessed).tree.newChild (Size.ofBytes data.input.offset) (.concrete data.input.parentTag) data.input.newTag
      (DedupRangeMap.new (Size.ofBytes data.input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree=child.tree := by
    simp only [child,GeneralBorrowExposedScopedDefaultExpression.child,GeneralBorrowExposedScopedDefaultExpression.read,
      data.treeEq,data.parentTagEq,data.newTagEq,data.offsetEq,data.lenEq]
  have treeEq := nextTree.trans childEq
  have childTags : GeneralBorrowGcAllocator.NodeTags child.tree := by rw [←childEq];exact metadata.1
  let nextData : GeneralBorrowExposedScopedMutableEntryRaw.Data child.tree protections exprTag future offset len selected head tail := {
    input := nextInput
    treeEq := treeEq
    parentTagEq := parentTagEq.trans data.newTagEq
    newTagEq := newTagEq
    offsetEq := offsetEq.trans data.offsetEq
    lenEq := lenEq.trans data.lenEq
    resources := raw
    nodeTags := by simpa only [GeneralBorrowGcAllocator.NodeTags,BorrowTree.indexOfTag,BorrowTree.nodeAt] using childTags }
  have helperClean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index nextInput)=none) nextInput.tree.locations := by
    have vacant : nextInput.tree.nodes.get (index nextInput)=none := by simp [UniValMap.get,at_end nextInput]
    rw [treeEq] at vacant ⊢
    have cleanChild : GeneralBorrowGcVacantClean.VacantClean child.tree := by rw [←childEq];exact metadata.2
    exact cleanChild (index nextInput) vacant
  refine ⟨nextData,parentEq,offsetEq.trans atBase,?_,helperClean⟩
  change nextInput.len=nextInput.tree.locations.size.bytes
  rw [lenEq,nextTree,geometry.2]
  exact full
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafNextRaw
