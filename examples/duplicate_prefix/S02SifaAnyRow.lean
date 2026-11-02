import duplicate_prefix.S02SifaAnyCallbacks
import duplicate_prefix.S02SifaRow

namespace DuplicatePrefix.S02SifaAnyRow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshOwnership DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual constructor SIFA preserves the full destination Row family on its
physical byte window, regardless of source/selected-root coincidence. -/
theorem owned (strongest : IdempotentForeignAccess) (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (protections : ProtectedTags) (source selected : Option UniIndex)
    (maximum : Option BorTag) (lower upper : UInt64)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (initial : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Row tree location protections source selected maximum)) lower upper tree.locations) :
    let after := (sourceUpdateSifa tree start strongest).1
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Row after location protections source selected maximum)) lower upper after.locations := by
  let after := (sourceUpdateSifa tree start strongest).1
  have callbacksBefore : GeneralRangeMapOrigins.OwnedOn (S02SifaCallbacks.Callbacks tree protections selected maximum)
      lower upper tree.locations := by
    intro position valid positive start stop
    obtain ⟨old⟩ := initial position valid positive start stop
    exact old.callbacks
  have callbacksAfter := S02SifaAnyCallbacks.owned strongest tree depth start protections selected maximum lower upper profile callbacksBefore
  have shape := GeneralBorrowSifaView.preserves tree start strongest
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have sizes := congrArg Array.size ranges
  simp only [Array.size_map] at sizes
  change GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (Row after location protections source selected maximum)) lower upper after.locations
  intro position valid positive start stop
  have previous : position < tree.locations.entries.size := by omega
  have known := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem previous,Option.map_some] at known
  have rangeEq := congrArg Prod.fst (Option.some.inj known)
  have locationEq := congrArg Prod.snd (Option.some.inj known)
  dsimp only [Prod.fst,Prod.snd] at rangeEq locationEq
  have oldStart := start
  have oldStop := stop
  rw [rangeEq] at oldStart oldStop
  obtain ⟨old⟩ := initial position previous positive oldStart oldStop
  exact S02SifaRow.row tree after _ _ protections source selected maximum shape locationEq old
    (callbacksAfter position valid positive start stop)

end DuplicatePrefix.S02SifaAnyRow
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SifaAnyRow.owned) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
