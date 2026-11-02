import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableEntryRaw
import duplicate_prefix.GeneralBorrowExposedScopedWritableProtectedMutableRun
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryConstructed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedScopedWritableMutableEntryRaw (Data)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def of_default (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    Data input.tree protections input.parentTag input.newTag input.offset input.len selected head tail := {
  input:=GeneralBorrowExposedScopedWritableMutableEntryInput.mutableInput input
  treeEq:=rfl
  parentTagEq:=rfl
  newTagEq:=rfl
  offsetEq:=rfl
  lenEq:=rfl
  resources:=GeneralBorrowExposedScopedWritableMutableEntryInput.mutableResources input protections selected head tail raw
  nodeTags:=nodeTags }

/-- Actual Strong registration, parent Read and protected mutable construction
retain the mixed writable-leaf data on the exact physical FnEntry child. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex)
    (data : Data tree protections parentTag newTag offset len selected head tail)
    (atBase : offset=0) (full : len=tree.locations.size.bytes) :
    let held:=protections.insert newTag .StrongProtector
    let read:=tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read held .VisitChildrenOfAccessed
    let child:=read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let anchor:=GeneralBorrowFreshMetadataChildMutable.index data.input
    let support:=fun position=>data.resources.component.support position ∨position=anchor.toNat
    read.status=.Completed ∧ child.outcome=.ok () ∧
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child.tree anchor selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data child.tree location held
        anchor selected head tail support (fun _=>true))) offset (offset+len) child.tree.locations := by
  obtain ⟨registered,sameSupport⟩:=GeneralBorrowExposedScopedWritableMutableEntryInput.register data.input protections selected head tail
    data.resources (by simpa only [data.treeEq] using data.nodeTags)
  have result:=GeneralBorrowExposedScopedWritableProtectedMutableRun.run data.input
    (protections.insert data.input.newTag .StrongProtector) selected head tail registered
    (by rw [data.offsetEq];exact atBase) (by rw [data.lenEq,data.treeEq];exact full) .VisitChildrenOfAccessed
  obtain ⟨readDone,childDone,context,owned⟩:=result
  simp only [data.treeEq,data.parentTagEq,data.newTagEq,data.offsetEq,data.lenEq,sameSupport] at readDone childDone context owned
  exact ⟨readDone,childDone,context,owned⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryConstructed
