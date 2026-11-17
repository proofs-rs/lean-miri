import duplicate_prefix.CurrentCallSpatialRows

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallSpatialRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private abbrev RowRuntime (tree : BorrowTree) (flags : ProtectedTags) (location : LocationTree) :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location flags ∧
  GeneralBorrowLocationSifaConsistency.Profile tree location flags ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location

private theorem cell_read {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte,Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (byte : AllocId × Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (segment : RangeMapSegment LocationTree)
    (member : segment ∈ role.backing.allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (rowRuntime : RowRuntime role.backing.allocation.extra tracker.global.protectedTags segment.data)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let actual := source_tree_access_at role.backing.allocation.extra segment.data (source role)
      .Read tracker.global.protectedTags visit range
    source_access_status actual=none ∧
      RowRuntime role.backing.allocation.extra tracker.global.protectedTags (source_access_location actual) ∧
      S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
        tracker.global.protectedTags (role.roles i overlap).grant (source_access_location actual) := by
  let W := singleByte role i overlap byte request cell
  obtain ⟨geometry⟩ := CurrentCallResourceNormalization.geometry_selected W
    (CandidateCurrentGrantRuntime.tree_rows role.backing.allocation.extra tracker.global runtime) exclusive
  have inside := singleByte_inside role i overlap byte request cell
  have sourceAt := source_at role i overlap
  cases value : role.family.value.provenance with
  | wildcard =>
    have wild : W.pointer.value.provenance=.wildcard := value
    have actual := CurrentCallResourceRead.wildcard_read W geometry exclusive byte inside segment member lower upper
      wild distinct rowRuntime.1 short rowRuntime.2.1 rowRuntime.2.2 visit range
    simp only [value] at sourceAt
    rw [sourceAt]
    exact ⟨actual.1,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,actual.2.2.2.2⟩
  | concrete id tag =>
    have concrete : ∃ id tag,W.pointer.value.provenance=.concrete id tag := ⟨id,tag,value⟩
    have actual := CurrentCallResourceRead.concrete_read W geometry exclusive byte inside segment member lower upper
      concrete distinct rowRuntime.1 short rowRuntime.2.1 rowRuntime.2.2 visit range
    simp only [value] at sourceAt
    rw [sourceAt]
    exact ⟨actual.1,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,actual.2.2.2.2.2⟩

/-- ONE actual range fold retains the SAME finite cell assignment and all of
its saved-row certificates. No callback chooses a fresh interpretation. -/
theorem access {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun _ => True)
      (RowRuntime role.backing.allocation.extra tracker.global.protectedTags) (Frame role) start (start+amount)
      (role.backing.allocation.extra.performBorrowAccessRange (provenance role) (Size.ofBytes start) (Size.ofBytes amount)
        .Read tracker.global.protectedTags visit) := by
  have positive : 0<length := by have positiveAmount : 0<amount.toNat := Nat.pos_of_ne_zero (fun zero => nonzero (UInt64.toNat_inj.mp zero));omega
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt role.backing.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat=offset+length := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap,startEq,amountEq]
  have initialRuntime : Every (RowRuntime role.backing.allocation.extra tracker.global.protectedTags) role.backing.allocation.extra.locations :=
    fun cursor valid => ⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid,runtime.possible cursor valid⟩
  have segmentRuntime : ∀ segment ∈ role.backing.allocation.extra.locations.entries.toList,
      RowRuntime role.backing.allocation.extra tracker.global.protectedTags segment.data := by
    intro segment member
    obtain ⟨cursor,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    exact initialRuntime cursor valid
  apply GeneralBorrowConcreteRangeEntry.access_resolved role.backing.allocation.extra tracker.global.protectedTags
    (provenance role) (source role) (resolved role positive) (Size.ofBytes start) (Size.ofBytes amount) .Read visit
    (Saved role) (fun _ => True) _ (Frame role) (fun _ _ => True.intro)
    (initial_authority role exclusive (fun segment member => (segmentRuntime segment member).2.1)
      (fun segment member => (segmentRuntime segment member).2.2)) _ start (start+amount)
    (saved_owned role start (start+amount) startEq endEq runtime.formed.well) runtime.formed.well initialRuntime
    bounds (Nat.le_refl _) (by change (start+amount).toNat≤(start+amount).toNat;exact Nat.le_refl _)
  intro location saved rowRuntime range
  obtain ⟨segment,member,same,byte,request,lower,upper⟩ := saved
  obtain ⟨i,cell⟩ := role.covered byte request
  let overlap : ∃ point,Window role.backing.id offset length point ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length point := ⟨byte,request,cell⟩
  have first := cell_read role exclusive runtime distinct short i overlap byte request cell segment member lower upper
    (same ▸ rowRuntime) visit range
  rw [same] at first
  refine ⟨first.1,True.intro,first.2.1,?_⟩
  intro original originalMember originalSame j joint hit
  obtain ⟨point,pointRequest,pointCell,pointLower,pointUpper⟩ := hit
  have allCells := cell_read role exclusive runtime distinct short j joint point pointRequest pointCell
    original originalMember pointLower pointUpper (originalSame ▸ rowRuntime) visit range
  rw [originalSame] at allCells
  exact allCells.2.2

/-- Actual runtime and EVERY fixed parent map follow the SAME range result. -/
theorem access_runtime {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    let actual := role.backing.allocation.extra.performBorrowAccessRange (provenance role) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags visit
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun _ => True)
      (RowRuntime role.backing.allocation.extra tracker.global.protectedTags) (Frame role) start (start+amount)
      (role.backing.allocation.extra.performBorrowAccessRange (provenance role) (Size.ofBytes start) (Size.ofBytes amount)
        .Read tracker.global.protectedTags visit) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts actual.tree tracker.global ∧
    ∀ i : Fin role.backing.cells.size, ParentInterpretation actual.tree role.backing.cells[i].completion := by
  have contract := access role exclusive runtime distinct short start amount startEq amountEq nonzero bounds visit
  refine ⟨contract,?_,?_⟩
  · rw [contract.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations role.backing.allocation.extra _ runtime.formed.toGraphState,contract.well⟩,?_⟩,
      ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (contract.runtime cursor valid).1
    · intro cursor valid
      exact (contract.runtime cursor valid).2.2
  · intro i
    let parents := role.backing.cells[i].parents
    rw [contract.tree_eq]
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations role.backing.allocation.extra _ parents.graph,
      parents.order,parents.dimension,parents.physical,parents.edgeLive,parents.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := parents.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {role.backing.allocation.extra with locations :=
        (role.backing.allocation.extra.performBorrowAccessRange (provenance role) (Size.ofBytes start)
          (Size.ofBytes amount) .Read tracker.global.protectedTags visit).tree.locations})
        (after := role.backing.allocation.extra) rfl path⟩


end
end DuplicatePrefix.CurrentCallSpatialRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Read dependency {dependency}"
