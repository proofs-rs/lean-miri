import duplicate_prefix.GeneralBorrowExposedConditionalRangeData
namespace DuplicatePrefix.GeneralBorrowExposedConditionalRangeFrames
open Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Position-preserving callback frames relative to the actual prepared map.
The original map may have a different segmentation after preparation. -/
def Rows (relation : α → α → Prop) (prepared current : DedupRangeMap α) : Prop :=
  ∀ position (valid : position < current.entries.size), ∃ before : position < prepared.entries.size,
    current.entries[position].range = prepared.entries[position].range ∧
      relation prepared.entries[position].data current.entries[position].data

def Origins (relation : α → α → Prop) (original current : DedupRangeMap α) : Prop :=
  ∀ point after, ValueAt current point after → ∃ before, ValueAt original point before ∧ relation before after

theorem rows_refl (relation : α → α → Prop) (map : DedupRangeMap α) (same : ∀ data,relation data data) :
    Rows relation map map := fun position valid => ⟨valid,rfl,same _⟩

theorem replaced_rows (relation : α → α → Prop) (prepared current : DedupRangeMap α)
    (position : Nat) (valid : position < current.entries.size) (data : α)
    (rows : Rows relation prepared current) (before : position < prepared.entries.size)
    (newFrame : relation prepared.entries[position].data data) :
    Rows relation prepared (replaced current position valid data) := by
  intro query bounded
  have oldBound : query < current.entries.size := by simpa only [replaced_length] using bounded
  obtain ⟨preparedBound,ranges,oldFrame⟩ := rows query oldBound
  refine ⟨preparedBound,?_,?_⟩
  · rw [replaced_range current position valid data query oldBound]
    exact ranges
  · by_cases same : position = query
    · subst query
      simpa only [replaced,Array.getElem_set_self] using newFrame
    · simpa only [replaced,Array.getElem_set_ne _ oldBound same] using oldFrame

theorem origins (relation : α → α → Prop) (original prepared current : DedupRangeMap α)
    (refined : Refines original prepared) (rows : Rows relation prepared current) :
    Origins relation original current := by
  intro point after witness
  obtain ⟨position,valid,start,stop,same⟩ := witness
  obtain ⟨before,ranges,frame⟩ := rows position valid
  have origin : ValueAt original point prepared.entries[position].data := by
    apply refined point prepared.entries[position].data
    refine ⟨position,before,?_,?_,rfl⟩
    · rw [←ranges];exact start
    · rw [←ranges];exact stop
  exact ⟨prepared.entries[position].data,origin,by simpa only [same] using frame⟩

theorem replaced_owned_on (predicate : α → Prop) (lower upper : UInt64)
    (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α)
    (owned : OwnedOn predicate lower upper map) (newGood : predicate data) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro query bounded positive start stop
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data query oldBound] at start stop
  by_cases same : position = query
  · subst query
    simpa only [replaced,Array.getElem_set_self] using newGood
  · simpa only [replaced,Array.getElem_set_ne _ oldBound same] using owned query oldBound positive start stop
end DuplicatePrefix.GeneralBorrowExposedConditionalRangeFrames
