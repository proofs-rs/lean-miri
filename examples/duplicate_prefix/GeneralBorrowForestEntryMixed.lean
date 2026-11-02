import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowForestMixedAccess
import duplicate_prefix.GeneralBorrowFreshMixedChild

namespace DuplicatePrefix.GeneralBorrowForestEntryMixed
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Mutable FnEntry records supply the first shared expression's all-writable
mixed input, including both actual foreign cache counter records. -/
def location (tree : BorrowTree) (where_ : LocationTree) (protections : ProtectedTags)
    (parent primary : UniIndex) (extras : List UniIndex)
    (data : GeneralBorrowForestMutableAccess.Data tree where_ protections parent primary extras) :
    GeneralBorrowForestMixedAccess.Data tree where_ protections parent primary extras (fun _ => true) where
  base := {
    forest := data.base.forest
    owned := GeneralBorrowRangePreserves.owned_for_access _ parent.toNat .Read .Write (by intro h;cases h) data.base.owned
    rootPath := data.base.rootPath
    region := GeneralBorrowForestMutableAccess.region tree where_ protections parent primary extras data .Read
    supported := data.base.supported
    foreignGraph := data.base.foreignGraph }
  mixed := (GeneralBorrowFreshMixedChild.write_combined tree where_ protections parent ⟨⟨data.base.forest⟩,data.base.owned⟩).2
  writeZero := data.base.region.zero

theorem owned (tree : BorrowTree) (protections : ProtectedTags)
    (parent primary : UniIndex) (extras : List UniIndex) (start stop : UInt64)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun point => Nonempty (GeneralBorrowForestMutableAccess.Data tree point protections parent primary extras))
      start stop tree.locations) :
    GeneralRangeMapOrigins.OwnedOn
      (fun point => Nonempty (GeneralBorrowForestMixedAccess.Data tree point protections parent primary extras (fun _ => true)))
      start stop tree.locations := by
  intro position valid present low high
  obtain ⟨data⟩ := before position valid present low high
  exact ⟨location tree _ protections parent primary extras data⟩

end DuplicatePrefix.GeneralBorrowForestEntryMixed
