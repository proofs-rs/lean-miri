import duplicate_prefix.GenericCopyMemoryCore

namespace DuplicatePrefix.ScopedCopyAccess
open Miri.ABI Miri.Memory Miri.TreeBorrows

/-- Internal copy boundary, derived from each caller's ownership input before
entering the shared MIR execution proof. Public caller contracts are unchanged. -/
def Completed (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset count : UInt64) : Prop :=
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset)
    (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count))
    (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
  read.status = .Completed ∧ write.status = .Completed

end DuplicatePrefix.ScopedCopyAccess
