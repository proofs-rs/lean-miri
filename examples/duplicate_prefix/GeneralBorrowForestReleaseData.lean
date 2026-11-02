import duplicate_prefix.GeneralBorrowForestRelease
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.GeneralBorrowForestReleaseData
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Data-only mutable protector-release input on arbitrary multiple roots. -/
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) where
  anchor : UniIndex
  primary : UniIndex
  extras : List UniIndex
  context : GeneralBorrowForestAccessData.Context tree anchor primary extras
  lower : UInt64
  upper : UInt64
  positive : lower.toNat < upper.toNat
  fits : tree.nodes.data.size ≤ 4294967296
  tagPresent : tree.indexOfTag tag = some anchor
  well : tree.locations.WellFormed
  within : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write lower upper
  owned : OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections anchor primary extras))
    lower upper tree.locations

/-- Execute the real implicit protector-end operations from data, without an
operation-success premise; activity confinement selects the owned window. -/
theorem released (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (input : Input tree protections tag) :
    (tree.releaseProtector tag protections).status = .Released :=
  (GeneralBorrowForestRelease.release tree protections tag input.anchor input.primary input.extras input.lower input.upper
    input.positive input.fits input.context input.tagPresent
    (GeneralBorrowFreshActiveWithin.active_on tree input.anchor .Write input.lower input.upper input.well input.within) input.owned).1

/-- Actual one-protector stack-pop plan, with its success derived internally. -/
theorem to_plan (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (input : Input entry.allocation.extra protections tag) :
    StackPopRelease.Plan protections [(id,tag)] memory
      (StackPopRelease.commitTree memory id entry (entry.allocation.extra.releaseProtector tag protections).tree) := by
  apply StackPopRelease.Plan.live id tag entry (entry.allocation.extra.releaseProtector tag protections).tree [] memory _ present
  · have done := released entry.allocation.extra protections tag input
    cases result : entry.allocation.extra.releaseProtector tag protections with
    | mk tree status => rw [result] at done;cases done;rfl
  · exact .nil _

end DuplicatePrefix.GeneralBorrowForestReleaseData
