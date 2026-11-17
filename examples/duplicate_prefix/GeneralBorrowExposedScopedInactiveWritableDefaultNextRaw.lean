import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryFromDefault
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultNextAllocator
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultNextGeometry
import duplicate_prefix.GeneralBorrowExposedScopedDefaultExpression
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultNextRaw
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Initial raw mutable-expression resources yield initial raw helper FnEntry
resources on the exact physical expression tree. Future-tag freshness, all
vacant-slot hygiene and helper-slot Clean are transported internally. -/
theorem next {profileMode : ProfileMode} (tree : BorrowTree) (protections : ProtectedTags) (parentTag exprTag future : BorTag) (offset len : UInt64)
    (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw.DataFor tree protections parentTag exprTag offset len selected head tail profileMode)
    (positive : data.input.offset.toNat<(data.input.offset+data.input.len).toNat)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping future) (different : exprTag≠future)
    (room : tree.nodes.size+2<65536) (vacantClean : GeneralBorrowGcVacantClean.VacantClean tree) :
    let child := GeneralBorrowExposedScopedDefaultExpression.child tree protections parentTag exprTag offset len .VisitChildrenOfAccessed
    ∃ next : GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw.DataFor child.tree protections exprTag future offset len selected head tail profileMode,
      next.input.parent=index data.input ∧ next.input.offset=offset ∧ next.input.len=len ∧
      GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index next.input)=none) next.input.tree.locations := by
  obtain ⟨done,nextInput,nextTree,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,raw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableDefaultNext.next_mode data.input protections selected head tail data.resources positive
      future (by simpa only [data.treeEq] using futureFresh) (by simpa only [data.newTagEq] using different)
      (by simpa only [data.treeEq] using room)
  have metadata := GeneralBorrowExposedScopedInactiveWritableDefaultNextAllocator.preserves_mode data.input protections selected head tail data.resources
    (by simpa only [data.treeEq] using data.nodeTags) (by simpa only [data.treeEq] using vacantClean)
  have geometry := GeneralBorrowExposedScopedInactiveWritableDefaultNextGeometry.frame data.input protections selected head tail data.resources
  let child := GeneralBorrowExposedScopedDefaultExpression.child tree protections parentTag exprTag offset len .VisitChildrenOfAccessed
  have childEq : ((data.input.tree.performBorrowAccessRange (.concrete data.input.parentTag) (Size.ofBytes data.input.offset) (Size.ofBytes data.input.len)
      .Read protections .VisitChildrenOfAccessed).tree.newChild (Size.ofBytes data.input.offset) (.concrete data.input.parentTag) data.input.newTag
      (DedupRangeMap.new (Size.ofBytes data.input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree=child.tree := by
    simp only [child,GeneralBorrowExposedScopedDefaultExpression.child,GeneralBorrowExposedScopedDefaultExpression.read,
      data.treeEq,data.parentTagEq,data.newTagEq,data.offsetEq,data.lenEq]
  have treeEq := nextTree.trans childEq
  have childTags : GeneralBorrowGcAllocator.NodeTags child.tree := by rw [←childEq];exact metadata.1
  let nextData : GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw.DataFor child.tree protections exprTag future offset len selected head tail profileMode := {
    input := nextInput
    treeEq := treeEq
    parentTagEq := parentTagEq.trans data.newTagEq
    newTagEq := newTagEq
    offsetEq := offsetEq.trans data.offsetEq
    lenEq := lenEq.trans data.lenEq
    resources := raw
    nodeTags := childTags }
  have helperClean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index nextInput)=none) nextInput.tree.locations := by
    have vacant : nextInput.tree.nodes.get (index nextInput)=none := by simp [UniValMap.get,at_end nextInput]
    rw [treeEq] at vacant ⊢
    have cleanChild : GeneralBorrowGcVacantClean.VacantClean child.tree := by rw [←childEq];exact metadata.2
    exact cleanChild (index nextInput) vacant
  let converted:=GeneralBorrowExposedScopedInactiveWritableMutableEntryFromDefault.convert child.tree protections exprTag future offset len selected head tail nextData
  exact ⟨converted,parentEq,offsetEq.trans data.offsetEq,lenEq.trans data.lenEq,helperClean⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultNextRaw
