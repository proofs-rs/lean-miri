import duplicate_prefix.GeneralBorrowSparseExposedRootAccessHistory
import duplicate_prefix.GeneralBorrowSparseExposedLeafCleanRange
namespace DuplicatePrefix.GeneralBorrowSparseExposedRootAccessResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedLeafHistory GeneralBorrowSparseExposedRootFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
private theorem full_every (predicate : α → Prop) (map : DedupRangeMap α) (well : map.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate 0 map.size.bytes map) : GeneralRangeMapState.Every predicate map := by
  intro position valid
  have facts := GeneralRangeMapGeometry.facts map well (by omega)
  have lastValid : map.entries.size-1 < map.entries.size := by omega
  have lastPositive := facts.2.1 (map.entries.size-1) lastValid
  have lastSize := GeneralRangeMapGeometry.size_last map (by omega)
  have positive := facts.2.1 position valid
  have startBound : map.entries[position].range.start.toNat < map.size.bytes.toNat := by
    rw [lastSize]
    by_cases same : position = map.entries.size-1
    · subst position;exact lastPositive
    · have before : position < map.entries.size-1 := by omega
      have separation := GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) before lastValid
      omega
  exact owned position valid (by simp only [UInt64.toNat_zero];omega) startBound (by simp only [UInt64.toNat_zero];omega)

theorem run_frame {capacity protections primary extras}
    (s : GeneralBorrowSparseExposedLeafHistory.State capacity protections primary extras) (events : List (Event capacity)) :
    (run s events).tree={s.tree with locations:=(run s events).tree.locations} := by
  induction events generalizing s with
  | nil=>rfl
  | cons event rest ih=>
    have first:=GeneralBorrowFreshReadFrame.frame s.tree .wildcard (Size.ofBytes event.offset) (Size.ofBytes event.len) event.kind protections event.mode
    change (build s event).state.tree={s.tree with locations:=(build s event).state.tree.locations} at first
    rw [show run s (event::rest)=run (build s event).state rest from rfl,ih,first]

theorem run_clean {capacity protections primary extras}
    (s : GeneralBorrowSparseExposedLeafHistory.State capacity protections primary extras)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.tree) (events : List (Event capacity)) :
    GeneralBorrowGcVacantClean.VacantClean (run s events).tree := by
  induction events generalizing s with
  | nil=>exact clean
  | cons event rest ih=>
    apply ih
    have frame:=GeneralBorrowFreshReadFrame.frame s.tree .wildcard (Size.ofBytes event.offset) (Size.ofBytes event.len) event.kind protections event.mode
    change (build s event).state.tree={s.tree with locations:=(build s event).state.tree.locations} at frame
    intro query vacant
    have previous : s.tree.nodes.get query=none := by rw [frame] at vacant;exact vacant
    have fits : event.offset.toNat+event.len.toNat<18446744073709551616 := by
      have bound:=UInt64.toNat_lt_size capacity;have request:=event.bounds;change capacity.toNat<18446744073709551616 at bound;omega
    have upper : (event.offset+event.len).toNat≤capacity.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits];exact event.bounds
    exact (GeneralBorrowSparseExposedLeafCleanRange.ranged s.tree protections primary query extras s.geometry
      (Size.ofBytes event.offset) (Size.ofBytes event.len) event.kind event.mode previous (clean query previous) s.well 0 capacity s.raw
      (by rw [s.capacityEq];exact event.bounds) (by change 0≤event.offset.toNat;omega) upper).2

/-- The actual finite access suffix retains graph, allocator, high-water and
vacant-slot resources in addition to the effective mixed writable protocol. -/
def finish {capacity} (s : GeneralBorrowSparseExposedRootFormation.State capacity) (events : List (Event capacity)) :
    GeneralBorrowSparseExposedRootFormation.State capacity := by
  let initial:=GeneralBorrowSparseExposedRootHistory.State.toAccess s
  let final:=run initial events
  have frame:=run_frame initial events
  have graph : GeneralBorrowStructuralHistoryState.GraphState final.tree := by
    rw [frame]
    exact GeneralBorrowStructuralHistoryState.graph_locations s.tree final.tree.locations s.structural.toGraphState
  have raw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw final.tree location s.global.protectedTags) final.tree.locations := by
    refine full_every (fun location=>GeneralBorrowSparseExposedLeafState.Raw final.tree location s.global.protectedTags) final.tree.locations final.well ?_
    have owned:=final.raw
    have capacityBytes : final.tree.locations.size.bytes=capacity := congrArg Size.bytes final.capacityEq
    rw [capacityBytes]
    exact owned
  exact {
    global:=s.global,tree:=final.tree,primary:=s.primary,extras:=s.extras,geometry:=final.geometry
    structural:=⟨graph,final.well⟩,raw:=raw,clean:=run_clean initial s.clean events
    noFree:=by rw [frame];exact s.noFree
    aligned:=by rw [frame];exact s.aligned
    capacityEq:=final.capacityEq,below:=by rw [frame];exact s.below }

end
end DuplicatePrefix.GeneralBorrowSparseExposedRootAccessResources
