import duplicate_prefix.S02SifaRow

namespace DuplicatePrefix.S02SifaPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView DuplicatePrefixBorrowAuthorization
set_option autoImplicit false

/-- Actual constructor SIFA preserves the complete positive destination
capability, including physical bounds and source presence. -/
theorem preserved (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (protections : ProtectedTags) (source selected : Option UniIndex)
    (maximum : Option BorTag) (offset len : UInt64)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (initial : Positive tree protections source selected maximum offset len) :
    let after := (sourceUpdateSifa tree start .Read).1
    Nonempty (Positive after protections source selected maximum offset len) := by
  let after := (sourceUpdateSifa tree start .Read).1
  have shape := GeneralBorrowSifaView.preserves tree start .Read
  have roots := GeneralBorrowFreshMetadata.roots tree after shape
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have rangeOnly : after.locations.entries.map (fun segment => segment.range) =
      tree.locations.entries.map (fun segment => segment.range) := by
    have := congrArg (fun rows => rows.map Prod.fst) ranges
    simpa only [Array.map_map,Function.comp_def] using this
  have capacity : after.locations.size = tree.locations.size := by
    rw [GeneralRangeMapState.size_from_ranges,GeneralRangeMapState.size_from_ranges,rangeOnly]
  refine ⟨{positive := initial.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩
  · rw [capacity];exact initial.bounds
  · intro anchor same
    obtain ⟨node,present⟩ := initial.sourcePresent anchor same
    obtain ⟨next,found,_⟩ := GeneralBorrowFreshMetadata.node_fields tree after shape anchor node present
    exact ⟨next,found⟩
  · intro wildcard
    rw [roots];exact initial.wildcardRoot wildcard
  · exact S02SifaRow.owned tree depth start protections source selected maximum offset (offset+len) profile initial.rows

end DuplicatePrefix.S02SifaPositive
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SifaPositive.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
