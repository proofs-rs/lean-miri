import duplicate_prefix.CurrentCallSpatialRows
namespace DuplicatePrefix.CurrentCallSpatialWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CandidateFreezeContentResources
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

variable {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)

/-- One actual scalar Write retains the SAME completion of every intersecting
cell; callers instantiate this theorem universally on the saved original row. -/
theorem row (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (segment : RangeMapSegment LocationTree) (member : segment∈role.backing.allocation.extra.locations.entries.toList)
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte,Window role.backing.id offset length byte ∧ Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (byte : AllocId × Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at role.backing.allocation.extra segment.data (CurrentCallSpatialRows.source role) .Write tracker.global.protectedTags visit range
    source_access_status result=none ∧
      GeneralBorrowExposureCardinality.LocationCoherent role.backing.allocation.extra (source_access_location result) tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra (source_access_location result) tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra (source_access_location result) ∧
      Authority role.backing.allocation.extra role.backing.cells[i].completion tracker.global.protectedTags
        (role.roles i overlap).grant (source_access_location result) := by
  let W := CurrentCallSpatialRows.singleByte role i overlap byte request cell
  obtain ⟨G⟩ := geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) exclusive
  obtain ⟨position,valid,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  have profile := runtime.formed.profile position valid
  have coherent := runtime.coherent position valid
  have possible := runtime.possible position valid
  rw [equal] at profile coherent possible
  have inside := CurrentCallSpatialRows.singleByte_inside role i overlap byte request cell
  cases provenance : role.family.value.provenance with
  | concrete supplied tag =>
    obtain ⟨node,present,mapped,binds⟩ := (role.roles i overlap).binding
    change (match role.family.value.provenance with | .concrete id tag => id=role.family.allocation ∧ tag=node.tag | .wildcard=>node.isExposed=true) at binds
    rw [provenance] at binds
    have lookup : role.backing.allocation.extra.indexOfTag tag=some (role.roles i overlap).grant := by rw [binds.2];exact mapped
    have actual := CurrentCallResourceAccess.concrete_write W G exclusive byte inside segment member lower upper ⟨supplied,tag,provenance⟩
      distinct coherent short profile possible visit range
    simp only [CurrentCallSpatialRows.source,provenance,lookup]
    have retained := actual.2.2.2.2.2
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals first | exact actual.1 | exact actual.2.1 | exact actual.2.2.1 | exact actual.2.2.2.1 | exact retained
  | wildcard =>
    have actual := CurrentCallResourceAccess.wildcard_write W G exclusive byte inside segment member lower upper provenance
      distinct coherent short profile possible visit range
    simpa only [W,CurrentCallSpatialRows.singleByte,CellRole.uniform,Family.at,CurrentCallSpatialRows.source,provenance] using actual

/-- Execute the actual full requested range once. Universal original-row frames
retain all cover-cell completions, even when proof cells and rows do not align. -/
theorem access (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
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
  have endEq : (start+amount).toNat=offset+length := by
    have fits : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds role.backing.allocation.extra.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits,startEq,amountEq]
  apply GeneralBorrowConcreteRangeEntry.access_resolved role.backing.allocation.extra tracker.global.protectedTags
    (CurrentCallSpatialRows.provenance role) (CurrentCallSpatialRows.source role) (CurrentCallSpatialRows.resolved role (by omega))
    (Size.ofBytes start) (Size.ofBytes amount) .Write visit (CurrentCallSpatialRows.Saved role) (fun _=>True)
    _ (CurrentCallSpatialRows.Frame role) (fun _ _=>trivial)
    (CurrentCallSpatialRows.initial_authority role exclusive profiles possibles) _ start (start+amount)
    (CurrentCallSpatialRows.saved_owned role start (start+amount) startEq endEq runtime.formed.well) runtime.formed.well
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
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
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
  have contract := access role exclusive runtime distinct short start amount startEq amountEq positive bounds visit
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
end DuplicatePrefix.CurrentCallSpatialWrite

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialWrite" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Write dependency {dependency}"
