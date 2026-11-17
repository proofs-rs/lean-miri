import duplicate_prefix.GeneralBorrowFullSharedSeed
import duplicate_prefix.GeneralBorrowFullSharedRepeat
import duplicate_prefix.GeneralBorrowSharedGeneratorWrite
namespace DuplicatePrefix.GeneralBorrowFullSharedWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedGeneratorWrite
/-- Lift the generated profile to the actual homogeneous range map. -/
theorem state_owned (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (good : GeneralBorrowFullSharedStep.State input location) :
    GeneralBorrowRange.LocationOwned input.tree {} input.parent .Write location ∧
    GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned input.tree {} input.parent .Write)
      input.offset (input.offset+input.len) input.tree.locations := by
  have owned : GeneralBorrowRange.LocationOwned input.tree {} input.parent .Write location :=
    ⟨good.forest,write_owned input location good.parentless good.profile⟩
  refine ⟨owned,?_⟩
  rw [good.locations]
  intro position valid _ _ _
  have zero : position = 0 := by
    change position < 1 at valid
    omega
  subst position
  exact owned

end DuplicatePrefix.GeneralBorrowFullSharedWrite
