import duplicate_prefix.GeneralRangeMapOriginPrepare
import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
import duplicate_prefix.GeneralRangeMapGeometry
namespace DuplicatePrefix.GeneralBorrowScopedFullDataFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapState
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
theorem every (map : DedupRangeMap LocationTree) (well : map.WellFormed) (predicate : LocationTree→Prop)
    (owned : OwnedOn predicate 0 map.size.bytes map) : Every predicate map := by
  intro position valid
  have nonempty : 0<map.entries.size := by omega
  have lastValid : map.entries.size-1<map.entries.size := by omega
  have lastSize := GeneralRangeMapGeometry.size_last map nonempty
  have positive := (GeneralRangeMapGeometry.facts map well (by omega)).2.1 position valid
  have upper : map.entries[position].range.stop.toNat≤map.size.bytes.toNat := by
    rw [lastSize]
    by_cases last : position=map.entries.size-1
    · subst position;exact Nat.le_refl _
    · have earlier : position<map.entries.size-1 := by omega
      have before := GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) earlier lastValid
      have lastPositive := (GeneralRangeMapGeometry.facts map well (by omega)).2.1 (map.entries.size-1) lastValid
      omega
  apply owned position valid
  all_goals try simp only [UInt64.toNat_zero]
  all_goals omega

/-- Positive full-range scoped data internally form the physical release
anchor's hidden flag. No final hidden-node certificate is requested. -/
theorem hidden (tree : BorrowTree) (protections : ProtectedTags) (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail) (kind : AccessKind)
    (well : tree.locations.WellFormed) (positive : (0:UInt64)<tree.locations.size.bytes)
    (owned : OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail kind))
      0 tree.locations.size.bytes tree.locations) : context.anchorNode.isExposed=false := by
  have nonempty : 0<tree.locations.entries.size := by
    apply Classical.byContradiction
    intro empty
    have size : tree.locations.entries.size=0 := by omega
    have nil : tree.locations.entries=#[] := Array.eq_empty_of_size_eq_zero size
    have zero : tree.locations.size.bytes=0 := by simp [DedupRangeMap.size,nil,Size.ZERO]
    rw [zero] at positive
    exact (UInt64.lt_irrefl _ positive)
  obtain ⟨data⟩ := every tree.locations well _ owned 0 nonempty
  exact data.hidden anchor context.anchorNode data.component.anchor context.anchorPresent
end DuplicatePrefix.GeneralBorrowScopedFullDataFlags
