import duplicate_prefix.GeneralRangeMapGeometry
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoFullRange
open Miri.ABI Miri.DataStructures
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A full-allocation slice predicate holds at every actual stored partition.
No singleton-partition or successful range-operation premise is needed. -/
theorem every (map : DedupRangeMap α) (predicate : α → Prop) (capacity : UInt64)
    (well : map.WellFormed) (size : map.size = Size.ofBytes capacity)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate 0 capacity map) :
    GeneralRangeMapState.Every predicate map := by
  intro position valid
  have nonempty : 0 < map.entries.size := by omega
  have facts := GeneralRangeMapGeometry.facts map well (by omega)
  have positive := facts.2.1 position valid
  have lastValid : map.entries.size-1 < map.entries.size := by omega
  have lastPositive := facts.2.1 (map.entries.size-1) lastValid
  have lastEnd := GeneralRangeMapGeometry.size_last map nonempty
  have sizeEq := congrArg (fun value : Size => value.bytes.toNat) size
  change map.size.bytes.toNat = capacity.toNat at sizeEq
  have endEq := congrArg UInt64.toNat lastEnd
  have stopBound : map.entries[position].range.stop.toNat ≤ capacity.toNat := by
    by_cases last : position = map.entries.size-1
    · subst position;omega
    · have order : position < map.entries.size-1 := by omega
      have earlier := GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) order lastValid
      omega
  exact owned position valid (by change 0 < capacity.toNat;omega) (by change map.entries[position].range.start.toNat < capacity.toNat;omega)
    (by change 0 < map.entries[position].range.stop.toNat;omega)
end DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoFullRange
