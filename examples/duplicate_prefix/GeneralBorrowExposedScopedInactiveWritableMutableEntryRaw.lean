import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
structure DataFor (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex) (profileMode : ProfileMode) where
  input : GeneralBorrowFreshMetadataChildMutable.Input
  treeEq : input.tree = tree
  parentTagEq : input.parentTag = parentTag
  newTagEq : input.newTag = newTag
  offsetEq : input.offset = offset
  lenEq : input.len = len
  resources : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor input protections selected head tail profileMode
  nodeTags : GeneralBorrowGcAllocator.NodeTags tree
/-- Legacy raw packet remains exactly the allocation-wide specialization. -/
abbrev Data (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex) :=
  DataFor tree protections parentTag newTag offset len selected head tail .global

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryRaw
