import duplicate_prefix.CurrentCallSpatialRead
import duplicate_prefix.CurrentCallSpatialWrite
import duplicate_prefix.CurrentCallSpatialSourceInstall
/-! A requested subrange uses the existing range fold while its certificate
retains the entire original spatial bank, including untouched source cells. -/
namespace DuplicatePrefix.CurrentCallSpatialSubrange.Read
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

private abbrev cell_read := spatial_install_rule ".CurrentCallSpatialRead.cell_read"

theorem saved_owned {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (lower upper : UInt64)
    (lowerBound : offset≤lower.toNat) (upperBound : upper.toNat≤offset+length)
    (well : role.backing.allocation.extra.locations.WellFormed) :
    OwnedOn (Saved role) lower upper role.backing.allocation.extra.locations := by
  intro position valid positive starts stops
  let segment := role.backing.allocation.extra.locations.entries[position]
  have member : segment ∈ role.backing.allocation.extra.locations.entries.toList:=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  refine ⟨segment,member,rfl,(role.backing.id,max lower.toNat segment.range.start.toNat),?_,?_,?_⟩
  · exact ⟨rfl,by omega,by dsimp only [segment] at *;omega⟩
  · omega
  · have nonempty := (GeneralRangeMapGeometry.facts role.backing.allocation.extra.locations well (by omega)).2.1 position valid
    dsimp only [segment]
    omega

/-- ONE actual range fold retains the SAME finite cell assignment and all of
its saved-row certificates. No callback chooses a fresh interpretation. -/
theorem access {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (start amount : UInt64) (lowerBound : offset≤start.toNat) (upperBound : start.toNat+amount.toNat≤offset+length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun _ => True)
      (RowRuntime role.backing.allocation.extra tracker.global.protectedTags) (Frame role) start (start+amount)
      (role.backing.allocation.extra.performBorrowAccessRange (provenance role) (Size.ofBytes start) (Size.ofBytes amount)
        .Read tracker.global.protectedTags visit) := by
  have positive : 0<length := by have positiveAmount : 0<amount.toNat := Nat.pos_of_ne_zero (fun zero => nonzero (UInt64.toNat_inj.mp zero));omega
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt role.backing.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat=start.toNat+amount.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
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
    (saved_owned role start (start+amount) lowerBound (by rw [endEq];exact upperBound) runtime.formed.well) runtime.formed.well initialRuntime
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
    (start amount : UInt64) (lowerBound : offset≤start.toNat) (upperBound : start.toNat+amount.toNat≤offset+length)
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
  have contract := access role exclusive runtime distinct short start amount lowerBound upperBound nonzero bounds visit
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
end DuplicatePrefix.CurrentCallSpatialSubrange.Read

namespace DuplicatePrefix.CurrentCallSpatialSubrange.Write
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CandidateFreezeContentResources
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

variable {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)

private abbrev row := @CurrentCallSpatialWrite.row

/-- Execute the actual full requested range once. Universal original-row frames
retain all cover-cell completions, even when proof cells and rows do not align. -/
theorem access (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (start amount : UInt64) (lowerBound : offset≤start.toNat) (upperBound : start.toNat+amount.toNat≤offset+length)
    (positive : 0<amount.toNat)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun _=>True)
      (fun location=>GeneralBorrowExposureCardinality.LocationCoherent role.backing.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra location)
      (CurrentCallSpatialRows.Frame role) start (start+amount)
      (role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount)
        .Write tracker.global.protectedTags visit) := by
  have profiles : ∀ segment∈role.backing.allocation.extra.locations.entries.toList,
      GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra segment.data tracker.global.protectedTags := by
    intro segment member
    obtain ⟨position,valid,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    rw [←equal];exact runtime.formed.profile position valid
  have possibles : ∀ segment∈role.backing.allocation.extra.locations.entries.toList,
      GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra segment.data := by
    intro segment member
    obtain ⟨position,valid,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    rw [←equal];exact runtime.possible position valid
  have endEq : (start+amount).toNat=start.toNat+amount.toNat := by
    have fits : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds role.backing.allocation.extra.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  apply GeneralBorrowConcreteRangeEntry.access_resolved role.backing.allocation.extra tracker.global.protectedTags
    (CurrentCallSpatialRows.provenance role) (CurrentCallSpatialRows.source role) (CurrentCallSpatialRows.resolved role (by omega))
    (Size.ofBytes start) (Size.ofBytes amount) .Write visit (CurrentCallSpatialRows.Saved role) (fun _=>True)
    _ (CurrentCallSpatialRows.Frame role) (fun _ _=>trivial)
    (CurrentCallSpatialRows.initial_authority role exclusive profiles possibles) _ start (start+amount)
    (CurrentCallSpatialSubrange.Read.saved_owned role start (start+amount) lowerBound (by rw [endEq];exact upperBound) runtime.formed.well) runtime.formed.well
    (fun position valid=>⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _)
  intro location saved representation range
  obtain ⟨segment,member,same,byte,request,lower,upper⟩ := saved
  obtain ⟨i,cell⟩ := role.covered byte request
  have overlap : ∃ point,Window role.backing.id offset length point ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length point := ⟨byte,request,cell⟩
  have selected := row role exclusive runtime distinct short segment member i overlap byte request cell lower upper visit range
  rw [same] at selected
  refine ⟨selected.1,trivial,⟨selected.2.1,selected.2.2.1,selected.2.2.2.1⟩,?_⟩
  intro oldSegment oldMember oldSame j oldOverlap hit
  obtain ⟨point,requestHit,cellHit,oldLower,oldUpper⟩ := hit
  have all := row role exclusive runtime distinct short oldSegment oldMember j oldOverlap point requestHit cellHit oldLower oldUpper visit range
  rw [oldSame] at all
  exact all.2.2.2.2

/-- Runtime and universal SAME-cover resources after the one actual range Write.
The output certificate is indexed by each original cell and its fixed completion. -/
theorem range (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (start amount : UInt64) (lowerBound : offset≤start.toNat) (upperBound : start.toNat+amount.toNat≤offset+length)
    (positive : 0<amount.toNat)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    let result := role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role)
      (Size.ofBytes start) (Size.ofBytes amount) .Write tracker.global.protectedTags visit
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun _=>True)
      (fun location=>GeneralBorrowExposureCardinality.LocationCoherent role.backing.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra location)
      (CurrentCallSpatialRows.Frame role) start (start+amount) result ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree tracker.global ∧
    (∀ i : Fin role.backing.cells.size,ParentInterpretation result.tree role.backing.cells[i].completion) ∧
    ∀ (point : UInt64) next,ValueAt result.tree.locations point next →
      Window role.backing.id offset length (role.backing.id,point.toNat) →
      ∀ (i : Fin role.backing.cells.size)
        (overlap : ∃ byte,Window role.backing.id offset length byte ∧ Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte),
        Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length (role.backing.id,point.toNat) →
        Authority result.tree role.backing.cells[i].completion tracker.global.protectedTags (role.roles i overlap).grant next := by
  let result := role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role)
    (Size.ofBytes start) (Size.ofBytes amount) .Write tracker.global.protectedTags visit
  have contract := access role exclusive runtime distinct short start amount lowerBound upperBound positive bounds visit
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts result.tree tracker.global := by
    rw [contract.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations role.backing.allocation.extra _ runtime.formed.toGraphState,contract.well⟩,?_⟩,
      ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (contract.runtime cursor valid).1
    · intro cursor valid
      exact (contract.runtime cursor valid).2.2
  refine ⟨contract,afterRuntime,?_,?_⟩
  · intro i
    let parents := role.backing.cells[i].parents
    rw [contract.tree_eq]
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations role.backing.allocation.extra _ parents.graph,
      parents.order,parents.dimension,parents.physical,parents.edgeLive,parents.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := parents.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {role.backing.allocation.extra with locations := result.tree.locations})
        (after := role.backing.allocation.extra) rfl path⟩
  · intro point next atPoint request i overlap cell index node present
    have retained := CurrentCallSpatialRows.recover role result.tree.locations contract.frames point next atPoint request i overlap cell
    exact retained index node (by rw [←contract.nodes];exact present)

end
end DuplicatePrefix.CurrentCallSpatialSubrange.Write


open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialSubrange" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved full-bank subrange dependency {dependency}"
