import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowForestMixedAccess
import duplicate_prefix.GeneralBorrowFreshMixedChild

namespace DuplicatePrefix.GeneralBorrowForestMixedInitial
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- Initial mutable records induce the mixed invariant with every old node
writable. Subsequent actual shared constructors mark only their new child
read-only; no permission or ownership postcondition is assumed. -/
def of_mutable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex)
    (data : GeneralBorrowForestMutableAccess.Data tree location protections anchor primary extras) :
    GeneralBorrowForestMixedAccess.Data tree location protections anchor primary extras (fun _ => true) where
  base := {
    forest := data.base.forest
    owned := GeneralBorrowFreshAnchor.anchor_readable _ anchor.toNat data.base.owned
    rootPath := data.base.rootPath
    region := GeneralBorrowForestMutableAccess.region tree location protections anchor primary extras data .Read
    supported := data.base.supported
    foreignGraph := data.base.foreignGraph }
  mixed := (GeneralBorrowFreshMixedChild.write_combined tree location protections anchor
    ⟨⟨data.base.forest⟩,data.base.owned⟩).2
  writeZero := data.base.region.zero

end DuplicatePrefix.GeneralBorrowForestMixedInitial
