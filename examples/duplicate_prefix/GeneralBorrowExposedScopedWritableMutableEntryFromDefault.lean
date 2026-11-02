import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultEntryRaw
import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryFromDefault
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]

/-- The ordinary input packet supplies the protected FnEntry input metadata
and initial resources verbatim; no operation outcome or stronger profile is
introduced by selecting the actual protected constructor policy. -/
def convert (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedWritableDefaultEntryRaw.Data tree protections parentTag newTag offset len selected head tail) :
    GeneralBorrowExposedScopedWritableMutableEntryRaw.Data tree protections parentTag newTag offset len selected head tail := {
  input:=GeneralBorrowExposedScopedWritableMutableEntryInput.mutableInput data.input
  treeEq:=data.treeEq
  parentTagEq:=data.parentTagEq
  newTagEq:=data.newTagEq
  offsetEq:=data.offsetEq
  lenEq:=data.lenEq
  resources:=GeneralBorrowExposedScopedWritableMutableEntryInput.mutableResources data.input protections selected head tail data.resources
  nodeTags:=data.nodeTags }

theorem index (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedWritableDefaultEntryRaw.Data tree protections parentTag newTag offset len selected head tail) :
    GeneralBorrowFreshMetadataChildMutable.index (convert tree protections parentTag newTag offset len selected head tail data).input=
      GeneralBorrowFreshMetadataChildDefault.index data.input := rfl
end DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryFromDefault
