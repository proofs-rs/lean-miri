import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultConstructor
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultEntryRaw
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Ordinary mutable-expression input; protected as_mut_ptr input uses the
separate WritableMutableEntryRaw packet. No operation result is a field. -/
structure Data (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex) where
  input : GeneralBorrowFreshMetadataChildDefault.Input
  treeEq : input.tree=tree
  parentTagEq : input.parentTag=parentTag
  newTagEq : input.newTag=newTag
  offsetEq : input.offset=offset
  lenEq : input.len=len
  resources : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail
  nodeTags : GeneralBorrowGcAllocator.NodeTags tree
end DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultEntryRaw
