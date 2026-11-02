import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedRun
import duplicate_prefix.GeneralBorrowExposedScopedSharedPathMetadata
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableSharedSourceSize
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Exact node growth of the actual Read/shared-child pipeline. -/
theorem child (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input protections selected head tail writable)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes) :
    (GeneralBorrowExposedScopedSharedPathMetadata.child input protections .VisitChildrenOfAccessed).nodes.size=input.tree.nodes.size+1 := by
  obtain ⟨_,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,_⟩ :=
    GeneralBorrowExposedScopedWritableSharedRun.prepare input protections selected head tail writable raw atBase full .VisitChildrenOfAccessed
  have frame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have nodes : prepared.tree.nodes=input.tree.nodes := by rw [treeEq,frame]
  have size:=(append prepared).size
  rw [nodes] at size
  simpa only [result,GeneralBorrowExposedScopedSharedPathMetadata.child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq,nodes] using size
end DuplicatePrefix.GeneralBorrowExposedScopedWritableSharedSourceSize
