import duplicate_prefix.GeneralBorrowForestReleaseData

namespace DuplicatePrefix.GeneralBorrowForestAsMutReleasePlan
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
abbrev Input := GeneralBorrowForestReleaseData.Input
noncomputable def release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) :=
  tree.releaseProtector tag protections
abbrev to_plan := GeneralBorrowForestReleaseData.to_plan
end DuplicatePrefix.GeneralBorrowForestAsMutReleasePlan
