import duplicate_prefix.GeneralBorrowSharedCapabilityRange
namespace DuplicatePrefix.GeneralBorrowSharedCapabilityShape
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowFreshOwnership GeneralBorrowProjection GeneralBorrowNodeUpdate GeneralRangeMapOrigins
open GeneralBorrowSharedCapabilityRange
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (protections : ProtectedTags) (parent child : UniIndex) (lower upper : UInt64)
    (owned : OwnedOn (Both before protections parent child) lower upper before.locations) :
    OwnedOn (Both after protections parent child) lower upper after.locations := by
  have nodes : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) :=
    congrArg (fun row => row.2.1) same
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid positive beforeUpper afterLower
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : (after.locations.entries[position]'valid).range =
        (before.locations.entries[position]'oldValid).range ∧
      locationShape (after.locations.entries[position]'valid).data =
        locationShape (before.locations.entries[position]'oldValid).data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem oldValid,Option.map_some] at known
    exact Prod.mk.inj (Option.some.inj known)
  rw [entriesSame.1] at beforeUpper afterLower
  obtain ⟨⟨normal⟩,⟨read⟩⟩ := owned position oldValid positive beforeUpper afterLower
  have profiles := GeneralBorrowFreshOwnership.projection_shape before after
    (before.locations.entries[position]'oldValid).data
    (after.locations.entries[position]'valid).data protections nodes entriesSame.2
  exact ⟨GeneralBorrowNormalCapabilityShape.normal before after _ _ protections parent profiles normal,
    GeneralBorrowNormalCapabilityShape.capability before after _ _ protections child .Read profiles read⟩

end DuplicatePrefix.GeneralBorrowSharedCapabilityShape
