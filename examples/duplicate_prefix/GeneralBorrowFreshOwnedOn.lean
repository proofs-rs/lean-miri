import duplicate_prefix.GeneralBorrowFreshOwnership
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.GeneralBorrowFreshOwnedOn
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- Shape equality preserves ownership only on the requested interval. Locations
outside that interval may have arbitrary permissions and protection history. -/
theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned before protections anchor kind) lower upper before.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned after protections anchor kind) lower upper after.locations := by
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
  obtain ⟨forest,owner⟩ := owned position oldValid positive beforeUpper afterLower
  have profiles := GeneralBorrowFreshOwnership.projection_shape before after
    (before.locations.entries[position]'oldValid).data
    (after.locations.entries[position]'valid).data protections nodes entriesSame.2
  refine ⟨?_,GeneralBorrowFreshOwnership.anchor_owned _ _ profiles anchor.toNat kind owner⟩
  have topology : (source_normal_projection after (after.locations.entries[position]'valid).data protections).topology =
      (source_normal_projection before (before.locations.entries[position]'oldValid).data protections).topology :=
    congrArg (fun row => row.1) profiles
  rw [topology]
  exact forest

/-- The actual ancestor SIFA update preserves range-local ownership. This
statement is data preservation; the constructor separately derives completion.
It imposes no ownership premise on disjoint allocation locations. -/
theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor kind) lower upper tree.locations) :
    let next := (sourceUpdateSifa tree start strongest).1
    OwnedOn (GeneralBorrowRange.LocationOwned next protections anchor kind) lower upper next.locations := by
  exact shape_preserves tree _ (GeneralBorrowSifaView.preserves tree start strongest)
    protections anchor kind lower upper owned
end DuplicatePrefix.GeneralBorrowFreshOwnedOn
#print axioms DuplicatePrefix.GeneralBorrowFreshOwnedOn.sifa_preserves
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshOwnedOn." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved range-local SIFA dependency {dependency}"
