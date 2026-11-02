import duplicate_prefix.GeneralBorrowScopedFullDataFlags
namespace DuplicatePrefix.GeneralBorrowScopedWindowDataFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxHeartbeats 1000000
/-- One genuine byte in an owned positive window determines the physical
anchor's hidden flag, without requiring ownership of disjoint bytes. -/
theorem hidden (tree : BorrowTree) (protections : ProtectedTags) (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail) (kind : AccessKind)
    (lower upper : UInt64) (well : tree.locations.WellFormed) (positive : lower.toNat<upper.toNat)
    (bounded : upper.toNat≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail kind))
      lower upper tree.locations) : context.anchorNode.isExposed=false := by
  obtain ⟨position,valid,start,stop⟩:=GeneralRangeMapGeometry.covered tree.locations well lower (by omega)
  obtain ⟨data⟩:=owned position valid positive (by omega) stop
  exact data.hidden anchor context.anchorNode data.component.anchor context.anchorPresent
end DuplicatePrefix.GeneralBorrowScopedWindowDataFlags
