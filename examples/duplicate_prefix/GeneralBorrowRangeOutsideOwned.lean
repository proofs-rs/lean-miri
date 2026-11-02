import duplicate_prefix.GeneralBorrowRangeOutside

/-! A disjoint byte window retains any initial row property across the actual
ranged access, on either outcome. Splitting changes row indices; the proof
observes one physical byte in each overlapping result segment. -/
namespace DuplicatePrefix.GeneralBorrowRangeOutsideOwned
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem owned (predicate : LocationTree → Prop) (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset len : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.bytes.toNat ∨ (offset.bytes+len.bytes).toNat ≤ point.toNat)
    (before : OwnedOn predicate lower upper tree.locations) :
    OwnedOn predicate lower upper
      (tree.performBorrowAccessRange provenance offset len kind protections mode).tree.locations := by
  let after := (tree.performBorrowAccessRange provenance offset len kind protections mode).tree.locations
  change OwnedOn predicate lower upper after
  intro position valid positive beforeUpper afterLower
  have frame := GeneralBorrowRangeOutside.outside_frame tree provenance offset len kind protections mode well bounds
    lower (disjoint lower (Nat.le_refl _) positive)
  have segmentPositive := (facts after frame.1 (by omega)).2.1 position valid
  have transfer : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      after.entries[position].range.start.toNat ≤ point.toNat →
      point.toNat < after.entries[position].range.stop.toNat → predicate after.entries[position].data := by
    intro point inLower inUpper inStart inStop
    have observed := (GeneralBorrowRangeOutside.outside_frame tree provenance offset len kind protections mode well bounds
      point (disjoint point inLower inUpper)).2.2 after.entries[position].data
      ⟨position,valid,inStart,inStop,rfl⟩
    obtain ⟨origin,bounded,oldStart,oldStop,same⟩ := observed
    have previous := before origin bounded positive (by omega) (by omega)
    simpa only [same] using previous
  by_cases earlier : lower.toNat ≤ after.entries[position].range.start.toNat
  · exact transfer after.entries[position].range.start earlier beforeUpper (by omega) segmentPositive
  · exact transfer lower (by omega) positive (by omega) afterLower

end DuplicatePrefix.GeneralBorrowRangeOutsideOwned

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRangeOutsideOwned." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved outside-window dependency {dependency}"
