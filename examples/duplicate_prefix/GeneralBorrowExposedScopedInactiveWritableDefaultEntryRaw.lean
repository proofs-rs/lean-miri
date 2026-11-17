import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultConstructor
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Ordinary mutable-expression input; protected as_mut_ptr input uses the
separate WritableMutableEntryRaw packet. No operation result is a field. -/
structure DataFor (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex) (profileMode : ProfileMode) where
  input : GeneralBorrowFreshMetadataChildDefault.Input
  treeEq : input.tree=tree
  parentTagEq : input.parentTag=parentTag
  newTagEq : input.newTag=newTag
  offsetEq : input.offset=offset
  lenEq : input.len=len
  resources : GeneralBorrowExposedScopedInactiveWritableDefaultConstructor.ResourcesFor input protections selected head tail profileMode
  nodeTags : GeneralBorrowGcAllocator.NodeTags tree
/-- Legacy raw packet remains exactly the allocation-wide specialization. -/
abbrev Data (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex) :=
  DataFor tree protections parentTag newTag offset len selected head tail .global

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultEntryRaw
