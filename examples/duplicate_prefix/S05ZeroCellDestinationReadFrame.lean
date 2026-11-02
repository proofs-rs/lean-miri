import duplicate_prefix.GeneralBorrowRangeOutside
import duplicate_prefix.S05ZeroCellCompletedBorrowModel

/-! Bind the pre-copy certificate to byte 1 after the actual source Read of
byte 0. This transports the destination row before its Write normal access;
it makes no claim about subsequent same-byte normal or wildcard callbacks. -/
namespace DuplicatePrefix.S05ZeroCellDestinationReadFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapByteLookup CandidateStableCallOwnership
open S05ZeroCellCurrentCorrelation (raw)
open S05ZeroCellTypedGeneratedPrefix (ix)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

abbrev afterRead : BorrowTree := S05ZeroCellActualCallRepaired.PureTree.read.tree

private theorem original_locations : raw.locations =
    DedupRangeMap.new (Size.ofBytes 2) S05ZeroCellCompletedBorrowModel.location := by
  obtain ⟨_,_,_,_,_,_,_,size,_,range,_⟩ := S05ZeroCellCurrentCorrelation.endpoint_identity
  have bound : 0 < raw.locations.entries.size := by omega
  let entry := raw.locations.entries[0]'bound
  have slot : raw.locations.entries[0]? = some entry := Array.getElem?_eq_getElem bound
  have entries : raw.locations.entries = #[entry] := by
    apply Array.ext
    · simpa only [Array.size_singleton] using size
    · intro index left right
      have zero : index = 0 := by omega
      subst index
      rfl
  have entryRange : entry.range = ⟨0,2⟩ := by
    simpa only [slot,Option.map_some,Option.some.injEq] using range
  have entryData : entry.data = S05ZeroCellCompletedBorrowModel.location := by
    simp only [S05ZeroCellCompletedBorrowModel.location,slot,Option.map_some,Option.getD_some]
  have segment : entry = ⟨⟨0,2⟩,S05ZeroCellCompletedBorrowModel.location⟩ := by
    rw [←entryRange,←entryData]
  have mapEq : raw.locations = {entries := #[entry]} := congrArg DedupRangeMap.mk entries
  rw [mapEq,segment]
  rfl

theorem original_well : raw.locations.WellFormed := by
  rw [original_locations]
  exact DedupRangeMap.new_wellFormed _ _

theorem original_capacity : raw.locations.size = Size.ofBytes 2 := by
  rw [original_locations]
  rfl

private theorem original_value : ValueAt raw.locations 1 S05ZeroCellCompletedBorrowModel.location := by
  rw [original_locations]
  exact ⟨0,by decide,by decide,by decide,rfl⟩

private theorem read_frame :
    afterRead.locations.WellFormed ∧ afterRead.locations.size = raw.locations.size ∧
      ∀ value, ValueAt afterRead.locations 1 value → ValueAt raw.locations 1 value := by
  exact GeneralBorrowRangeOutside.outside_frame raw
    (.concrete S05ZeroCellActualCallRepaired.PureTree.tag) Size.ZERO (Size.ofBytes 1)
    .Read S05ZeroCellCurrentCorrelation.held .VisitChildrenOfAccessed original_well
    (by rw [original_capacity];decide) 1 (.inr (by decide))

/-- Actual source Read, actual provenance/tag/protectors, disjoint destination
byte. The frame theorem uses no Read-completion premise. -/
theorem destination_lookup :
    lookup afterRead.locations 1 = .ok S05ZeroCellCompletedBorrowModel.location := by
  have unchanged := GeneralBorrowRangeOutside.lookup_outside raw
    (.concrete S05ZeroCellActualCallRepaired.PureTree.tag) Size.ZERO (Size.ofBytes 1)
    .Read S05ZeroCellCurrentCorrelation.held .VisitChildrenOfAccessed original_well
    (by rw [original_capacity];decide) 1 (by rw [original_capacity];decide) (.inr (by decide))
  exact unchanged.trans (lookup_of_value raw.locations original_well 1 _ original_value)

theorem destination_value : ValueAt afterRead.locations 1 S05ZeroCellCompletedBorrowModel.location := by
  obtain ⟨value,observed,actual⟩ := lookup_success afterRead.locations read_frame.1 1
    (by rw [read_frame.2.1,original_capacity];decide)
  have same : value = S05ZeroCellCompletedBorrowModel.location :=
    Except.ok.inj (actual.symm.trans destination_lookup)
  simpa only [same] using observed

theorem destination_segment (position : Nat) (valid : position < afterRead.locations.entries.size)
    (start : afterRead.locations.entries[position].range.start.toNat ≤ 1)
    (stop : 1 < afterRead.locations.entries[position].range.stop.toNat) :
    afterRead.locations.entries[position].data = S05ZeroCellCompletedBorrowModel.location :=
  value_unique afterRead.locations read_frame.1 1 _ _ ⟨position,valid,start,stop,rfl⟩ destination_value

theorem graph_preserved : afterRead.nodes = raw.nodes ∧ afterRead.roots = raw.roots ∧
    afterRead.tagMapping = raw.tagMapping := by cbv

theorem local_rights (position : Nat) (valid : position < afterRead.locations.entries.size)
    (start : afterRead.locations.entries[position].range.start.toNat ≤ 1)
    (stop : 1 < afterRead.locations.entries[position].range.stop.toNat)
    {index : UniIndex} {actual : TreeNode} (present : afterRead.nodes.get index = some actual)
    (ancestor : Below S05ZeroCellCompletedBorrowModel.completion index (ix 10)) :
    OrdinaryBorrowAuthority.LocalWrite
      ((afterRead.locations.entries[position].data.perms.get index).getD actual.defaultLocationState)
      (S05ZeroCellCurrentCorrelation.held.contains actual.tag) := by
  rw [destination_segment position valid start stop]
  rw [graph_preserved.1] at present
  exact S05ZeroCellCompletedBorrowModel.local_rights present ancestor

theorem foreign_rights (position : Nat) (valid : position < afterRead.locations.entries.size)
    (start : afterRead.locations.entries[position].range.start.toNat ≤ 1)
    (stop : 1 < afterRead.locations.entries[position].range.stop.toNat)
    {index : UniIndex} {actual : TreeNode} (present : afterRead.nodes.get index = some actual)
    (outside : ¬ Below S05ZeroCellCompletedBorrowModel.completion index (ix 10)) :
    OrdinaryBorrowAuthority.ForeignWrite
      ((afterRead.locations.entries[position].data.perms.get index).getD actual.defaultLocationState)
      (S05ZeroCellCurrentCorrelation.held.contains actual.tag) := by
  rw [destination_segment position valid start stop]
  rw [graph_preserved.1] at present
  exact S05ZeroCellCompletedBorrowModel.foreign_rights present outside

theorem consistent (position : Nat) (valid : position < afterRead.locations.entries.size)
    (start : afterRead.locations.entries[position].range.start.toNat ≤ 1)
    (stop : 1 < afterRead.locations.entries[position].range.stop.toNat)
    {index : UniIndex} {actual : TreeNode} (present : afterRead.nodes.get index = some actual) :
    GeneralBorrowSifaPermissionConsistency.Consistent
      ((afterRead.locations.entries[position].data.perms.get index).getD actual.defaultLocationState)
      (S05ZeroCellCurrentCorrelation.held.contains actual.tag) := by
  rw [destination_segment position valid start stop]
  rw [graph_preserved.1] at present
  exact S05ZeroCellCompletedBorrowModel.consistent present

end DuplicatePrefix.S05ZeroCellDestinationReadFrame

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellDestinationReadFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved destination Read frame dependency {dependency}"
