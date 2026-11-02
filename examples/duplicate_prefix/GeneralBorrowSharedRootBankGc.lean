import duplicate_prefix.GeneralBorrowGcRootResources
import duplicate_prefix.GeneralBorrowSharedRootBankGeneration
namespace DuplicatePrefix.GeneralBorrowSharedRootBankGc
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedRootBankGeneration DuplicatePrefix.GeneralBorrowGcRootResources
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Collect an actual arbitrary-depth branching bank, internally retaining the
original mutable root and forming every next invocation resource. -/
def collect {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping (reserve i))
    (live : Array BorTag) : Collected s.bank.tree root rootTag tag offset len reserve live := by
  let data := GeneralBorrowSharedRootBankState.entryData s tag fresh
  have owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned s.bank.tree {} root .Write)
      offset (offset+len) s.bank.tree.locations := data.owned
  let node := Classical.choose s.rootPresent
  have present := (Classical.choose_spec s.rootPresent).1
  have tagged := (Classical.choose_spec s.rootPresent).2
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have forest := GeneralBorrowFreshDefaultPathData.forest_of_owned s.bank.tree {} root offset len positive
    s.bank.resources.well s.bank.bounds owned location {}
  have parent := GeneralBorrowGcRootResources.parentless s.bank.tree root node location forest present (s.rootPath location)
  exact GeneralBorrowGcRootResources.collect s.bank.tree root rootTag tag offset len s.bank.resources node present tagged parent
    positive s.bank.bounds owned fresh reserve reserved live
end
end DuplicatePrefix.GeneralBorrowSharedRootBankGc
