import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallOptionalObserverReadCapability

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallSpatialObserverRead
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

theorem cell_read {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some parent) (hidden : readerNode.isExposed=false)
    (unheld : tracker.global.protectedTags.contains readerNode.tag=false)
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte,Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (byte : AllocId × Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (segment : RangeMapSegment LocationTree)
    (member : segment ∈ role.backing.allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (rowRuntime : RowRuntime role.backing.allocation.extra tracker.global.protectedTags segment.data)
    (readable : DuplicatePrefixNormalKind.Capability role.backing.allocation.extra segment.data tracker.global.protectedTags reader .Read)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let actual := source_tree_access_at role.backing.allocation.extra segment.data (some reader)
      .Read tracker.global.protectedTags visit range
    source_access_status actual=none ∧
      RowRuntime role.backing.allocation.extra tracker.global.protectedTags (source_access_location actual) ∧
      S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
        tracker.global.protectedTags (role.roles i overlap).grant (source_access_location actual) ∧
      Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra (source_access_location actual) tracker.global.protectedTags reader .Read) := by
  let W := singleByte role i overlap byte request cell
  obtain ⟨geometry⟩ := CurrentCallResourceNormalization.geometry_selected W
    (CandidateCurrentGrantRuntime.tree_rows role.backing.allocation.extra tracker.global runtime) exclusive
  have inside := singleByte_inside role i overlap byte request cell
  have sourceAt := source_at role i overlap
  simp only [concrete] at sourceAt
  have grantEq : (role.roles i overlap).grant=parent := by
    have look : source role=some parent := by simp only [source,concrete];exact tagged
    exact Option.some.inj (sourceAt.symm.trans look)
  have authority := CurrentCallSpatialRows.initial_authority role exclusive
    (fun s mem => by obtain ⟨cursor,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp mem);subst s;exact runtime.formed.profile cursor valid)
    (fun s mem => by obtain ⟨cursor,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp mem);subst s;exact runtime.possible cursor valid)
    segment.data segment member rfl i overlap ⟨byte,request,cell,lower,upper⟩
  have futureAuthority : S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
      (tracker.global.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag)).protectedTags parent segment.data := by
    intro index node present
    rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags") tracker.global role.backing.id readerNode.tag node.tag (.inl unheld)]
    simpa only [grantEq] using authority index node present
  have sourcePath := geometry.sourcePath
  change GeneralBorrowExposedNonleafPrimaryPath.Path _ _ (role.roles i overlap).grant at sourcePath
  rw [grantEq] at sourcePath
  have primarySlot := W.issued.capability.rootSlot
  have grounded := geometry.grounded
  change Below role.backing.cells[i].completion allocationRoot (role.roles i overlap).grant at grounded
  rw [grantEq] at grounded
  have actual := CurrentCallOptionalObserverReadCapability.direct role.backing.allocation.extra role.backing.cells[i].completion
    segment.data tracker.global runtime role.backing.cells[i].parents primarySlot distinct role.backing.cells[i].parents.order
    geometry.selectedPosition geometry.selectedRoot parent reader geometry.selectedNode readerNode
    grounded geometry.selectedSlot geometry.selectedAt sourcePath readerAt
    (.step sourcePath readerNode readerAt readerEdge) role.backing.id readerEdge hidden readable futureAuthority
    rowRuntime.1 rowRuntime.2.1 rowRuntime.2.2 short visit range
  refine ⟨actual.1,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,?_,actual.2.2.2.2.2⟩
  intro index node present
  have result := actual.2.2.2.2.1 index node present
  rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags") tracker.global role.backing.id readerNode.tag node.tag (.inl unheld)] at result
  simpa only [grantEq] using result

theorem access {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some parent) (hidden : readerNode.isExposed=false)
    (unheld : tracker.global.protectedTags.contains readerNode.tag=false)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability
      role.backing.allocation.extra location tracker.global.protectedTags reader .Read)) start (start+amount) role.backing.allocation.extra.locations)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location tracker.global.protectedTags reader .Read))
      (RowRuntime role.backing.allocation.extra tracker.global.protectedTags) (Frame role) start (start+amount)
      (role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
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
  have capability : ∀ segment ∈ role.backing.allocation.extra.locations.entries.toList,
      (∃byte, Window role.backing.id offset length byte ∧segment.range.start.toNat≤byte.2 ∧byte.2<segment.range.stop.toNat) →
      Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra segment.data tracker.global.protectedTags reader .Read) := by
    intro segment member hit
    obtain ⟨byte,request,lo,hi⟩:=hit
    obtain ⟨cursor,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have requestLower := request.2.1
    have requestUpper := request.2.2
    exact readable cursor valid (by omega) (by omega) (by omega)
  apply GeneralBorrowConcreteRangeEntry.access_resolved role.backing.allocation.extra tracker.global.protectedTags
    (.concrete readerNode.tag) (some reader) (by exact ⟨reader,runtime.formed.allocator.nodeTags reader readerNode readerAt,rfl⟩) (Size.ofBytes start) (Size.ofBytes amount) .Read visit
    (Saved role) (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location tracker.global.protectedTags reader .Read)) _ (Frame role) (by
      intro location saved
      obtain ⟨segment,member,same,byte,request,lower,upper⟩:=saved
      rw [←same]
      exact capability segment member ⟨byte,request,lower,upper⟩)
    (initial_authority role exclusive (fun segment member => (segmentRuntime segment member).2.1)
      (fun segment member => (segmentRuntime segment member).2.2)) _ start (start+amount)
    (saved_owned role start (start+amount) startEq endEq runtime.formed.well) runtime.formed.well initialRuntime
    bounds (Nat.le_refl _) (by change (start+amount).toNat≤(start+amount).toNat;exact Nat.le_refl _)
  intro location saved rowRuntime range
  obtain ⟨segment,member,same,byte,request,lower,upper⟩ := saved
  obtain ⟨i,cell⟩ := role.covered byte request
  let overlap : ∃ point,Window role.backing.id offset length point ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length point := ⟨byte,request,cell⟩
  have first := cell_read role exclusive runtime distinct short parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld i overlap byte request cell segment member lower upper
    (same ▸ rowRuntime) (Classical.choice (capability segment member ⟨byte,request,lower,upper⟩)) visit range
  rw [same] at first
  refine ⟨first.1,first.2.2.2,first.2.1,?_⟩
  intro original originalMember originalSame j joint hit
  obtain ⟨point,pointRequest,pointCell,pointLower,pointUpper⟩ := hit
  have allCells := cell_read role exclusive runtime distinct short parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld j joint point pointRequest pointCell
    original originalMember pointLower pointUpper (originalSame ▸ rowRuntime) (Classical.choice (capability original originalMember ⟨point,pointRequest,pointLower,pointUpper⟩)) visit range
  rw [originalSame] at allCells
  exact allCells.2.2.1

theorem access_runtime {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some parent) (hidden : readerNode.isExposed=false)
    (unheld : tracker.global.protectedTags.contains readerNode.tag=false)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability
      role.backing.allocation.extra location tracker.global.protectedTags reader .Read)) start (start+amount) role.backing.allocation.extra.locations)
    (visit : ChildrenVisitMode) :
    let actual := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags visit
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location tracker.global.protectedTags reader .Read))
      (RowRuntime role.backing.allocation.extra tracker.global.protectedTags) (Frame role) start (start+amount)
      (role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
        .Read tracker.global.protectedTags visit) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts actual.tree tracker.global ∧
    ∀ i : Fin role.backing.cells.size, ParentInterpretation actual.tree role.backing.cells[i].completion := by
  have contract := access role exclusive runtime distinct short parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld start amount startEq amountEq nonzero bounds readable visit
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
        (role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start)
          (Size.ofBytes amount) .Read tracker.global.protectedTags visit).tree.locations})
        (after := role.backing.allocation.extra) rfl path⟩
end
end DuplicatePrefix.CurrentCallSpatialObserverRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialObserverRead" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial observer Read dependency {dependency}"
