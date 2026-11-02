import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallOptionalObserverRelease
import duplicate_prefix.CurrentCallOptionalLenAssociatedRead

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallSpatialLenRelease
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
    (current : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra current)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (temporary : UniIndex) (temporaryNode : TreeNode)
    (temporaryAt : role.backing.allocation.extra.nodeAt temporary=some temporaryNode)
    (readerEdge : readerNode.parent=some temporary) (temporaryEdge : temporaryNode.parent=some parent)
    (hidden : readerNode.isExposed=false) (temporaryHidden : temporaryNode.isExposed=false)
    (temporaryUnheld : current.protectedTags.contains temporaryNode.tag=false)
    (futureEq : tracker.global=current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag))
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte,Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (byte : AllocId × Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (segment : RangeMapSegment LocationTree)
    (member : segment ∈ role.backing.allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (rowRuntime : RowRuntime role.backing.allocation.extra current.protectedTags segment.data)
    (readable : DuplicatePrefixNormalKind.Capability role.backing.allocation.extra segment.data current.protectedTags reader .Read)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let actual := source_tree_access_at role.backing.allocation.extra segment.data (some reader)
      .Read current.protectedTags visit range
    source_access_status actual=none ∧
      RowRuntime role.backing.allocation.extra current.protectedTags (source_access_location actual) ∧
      S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
        tracker.global.protectedTags (role.roles i overlap).grant (source_access_location actual) := by
  obtain ⟨firstRuntime,_,_⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call role.backing.allocation.extra current runtime
    role.backing.id readerNode.tag reader readerNode readerAt rfl hidden
  have futureRuntime:=firstRuntime
  rw [←futureEq] at futureRuntime
  have unheldAfter : (current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag)).protectedTags.contains temporaryNode.tag=false := by
    by_cases same : temporaryNode.tag=readerNode.tag
    · rw [same]
      change (current.protectedTags.remove readerNode.tag).contains readerNode.tag=false
      simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    · rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags") current role.backing.id readerNode.tag temporaryNode.tag (.inr same)]
      exact temporaryUnheld
  let W := singleByte role i overlap byte request cell
  obtain ⟨geometry⟩ := CurrentCallResourceNormalization.geometry_selected W
    (CandidateCurrentGrantRuntime.tree_rows role.backing.allocation.extra tracker.global futureRuntime) exclusive
  have inside := singleByte_inside role i overlap byte request cell
  have sourceAt := source_at role i overlap
  simp only [concrete] at sourceAt
  have grantEq : (role.roles i overlap).grant=parent := by
    have look : source role=some parent := by simp only [source,concrete];exact tagged
    exact Option.some.inj (sourceAt.symm.trans look)
  have authority := CurrentCallSpatialRows.initial_authority role exclusive
    (fun s mem => by obtain ⟨cursor,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp mem);subst s;exact futureRuntime.formed.profile cursor valid)
    (fun s mem => by obtain ⟨cursor,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp mem);subst s;exact futureRuntime.possible cursor valid)
    segment.data segment member rfl i overlap ⟨byte,request,cell,lower,upper⟩
  have sourcePath := geometry.sourcePath
  change GeneralBorrowExposedNonleafPrimaryPath.Path _ _ (role.roles i overlap).grant at sourcePath
  rw [grantEq] at sourcePath
  have primarySlot := W.issued.capability.rootSlot
  have grounded := geometry.grounded
  change Below role.backing.cells[i].completion allocationRoot (role.roles i overlap).grant at grounded
  rw [grantEq] at grounded
  have actual := CurrentCallOptionalObserverRelease.access_two role.backing.allocation.extra role.backing.cells[i].completion
    segment.data current runtime role.backing.cells[i].parents primarySlot distinct role.backing.cells[i].parents.order
    geometry.selectedPosition geometry.selectedRoot parent reader geometry.selectedNode readerNode
    grounded geometry.selectedSlot geometry.selectedAt sourcePath readerAt
    (.step (.step sourcePath temporaryNode temporaryAt temporaryEdge) readerNode readerAt readerEdge) role.backing.id temporary temporaryNode readerEdge temporaryAt temporaryEdge hidden temporaryHidden readable
    (by
      intro index node present
      rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags")
        (current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag)) role.backing.id temporaryNode.tag node.tag (.inl unheldAfter)]
      rw [←futureEq]
      simpa only [grantEq] using authority index node present)
    rowRuntime.1 rowRuntime.2.1 rowRuntime.2.2 short visit range
  refine ⟨actual.1,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,?_⟩
  intro index node present
  have retained:=actual.2.2.2.2 index node present
  rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags")
    (current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag)) role.backing.id temporaryNode.tag node.tag (.inl unheldAfter),←futureEq] at retained
  simpa only [grantEq] using retained

private theorem row_read {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (current : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra current)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (temporary : UniIndex) (temporaryNode : TreeNode)
    (temporaryAt : role.backing.allocation.extra.nodeAt temporary=some temporaryNode)
    (readerEdge : readerNode.parent=some temporary) (temporaryEdge : temporaryNode.parent=some parent)
    (hidden : readerNode.isExposed=false) (temporaryHidden : temporaryNode.isExposed=false)
    (temporaryUnheld : current.protectedTags.contains temporaryNode.tag=false)
    (futureEq : tracker.global=current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag))
    (segment : RangeMapSegment LocationTree) (member : segment∈role.backing.allocation.extra.locations.entries.toList)
    (byte : AllocId×Nat) (request : Window role.backing.id offset length byte)
    (lower : segment.range.start.toNat≤byte.2) (upper : byte.2<segment.range.stop.toNat)
    (rowRuntime : RowRuntime role.backing.allocation.extra current.protectedTags segment.data)
    (readable : DuplicatePrefixNormalKind.Capability role.backing.allocation.extra segment.data current.protectedTags reader .Read)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let actual:=source_tree_access_at role.backing.allocation.extra segment.data (some reader) .Read current.protectedTags visit range
    source_access_status actual=none ∧RowRuntime role.backing.allocation.extra current.protectedTags (source_access_location actual) ∧
    CurrentCallSpatialRows.Frame role segment.data (source_access_location actual) := by
  obtain ⟨i,cell⟩:=role.covered byte request
  let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨byte,request,cell⟩
  have result:=cell_read role exclusive current runtime distinct short parentTag parent reader readerNode concrete tagged readerAt
    temporary temporaryNode temporaryAt readerEdge temporaryEdge hidden temporaryHidden temporaryUnheld futureEq i overlap byte request cell
    segment member lower upper rowRuntime readable visit range
  refine ⟨result.1,result.2.1,?_⟩
  intro original originalMember same j joint hit
  obtain ⟨point,pointRequest,pointCell,pointLower,pointUpper⟩:=hit
  have all:=cell_read role exclusive current runtime distinct short parentTag parent reader readerNode concrete tagged readerAt
    temporary temporaryNode temporaryAt readerEdge temporaryEdge hidden temporaryHidden temporaryUnheld futureEq j joint point pointRequest pointCell
    original originalMember pointLower pointUpper (same ▸ rowRuntime) (same ▸ readable) visit range
  rw [same] at all
  exact all.2.2

theorem release {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (current : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra current)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (temporary : UniIndex) (temporaryNode : TreeNode)
    (temporaryAt : role.backing.allocation.extra.nodeAt temporary=some temporaryNode)
    (readerEdge : readerNode.parent=some temporary) (temporaryEdge : temporaryNode.parent=some parent)
    (hidden : readerNode.isExposed=false) (temporaryHidden : temporaryNode.isExposed=false)
    (temporaryUnheld : current.protectedTags.contains temporaryNode.tag=false)
    (futureEq : tracker.global=current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag))
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat) (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra reader .Read start (start+amount))
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location current.protectedTags reader .Read))
      start (start+amount) role.backing.allocation.extra.locations) :
    let result:=role.backing.allocation.extra.releaseProtector readerNode.tag current.protectedTags
    result.status=.Released ∧result.tree={role.backing.allocation.extra with locations:=result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree current ∧result.tree.locations.size=role.backing.allocation.extra.locations.size ∧
    S05CurrentReleaseIterator.Rows (fun range location =>∃ original∈role.backing.allocation.extra.locations.entries.toList,
      original.range=range ∧CurrentCallSpatialRows.Frame role original.data location) result.tree.locations := by
  let saved:=fun range location=>∃ original∈role.backing.allocation.extra.locations.entries.toList,
    original.range=range ∧CurrentCallSpatialRows.Frame role original.data location
  let P:=fun range location=>RowRuntime role.backing.allocation.extra current.protectedTags location ∧saved range location
  obtain ⟨firstRuntime,_,_⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call role.backing.allocation.extra current runtime
    role.backing.id readerNode.tag reader readerNode readerAt rfl hidden
  have futureRuntime:=firstRuntime
  rw [←futureEq] at futureRuntime
  have unheldAfter : (current.endCall (({} : FrameState).addProtector role.backing.id readerNode.tag)).protectedTags.contains temporaryNode.tag=false := by
    by_cases same : temporaryNode.tag=readerNode.tag
    · rw [same]
      change (current.protectedTags.remove readerNode.tag).contains readerNode.tag=false
      simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    · rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags") current role.backing.id readerNode.tag temporaryNode.tag (.inr same)]
      exact temporaryUnheld
  have initialFrames:=CurrentCallSpatialRows.initial_authority role exclusive
    (by intro segment member;obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member);rw [←same];exact futureRuntime.formed.profile position valid)
    (by intro segment member;obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member);rw [←same];exact futureRuntime.possible position valid)
  have rows : S05CurrentReleaseIterator.Rows P role.backing.allocation.extra.locations:=by
    intro position valid
    exact ⟨⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩,
      role.backing.allocation.extra.locations.entries[position],Array.mem_toList_iff.mpr (Array.getElem_mem valid),rfl,initialFrames _⟩
  have mapped:=runtime.formed.allocator.nodeTags reader readerNode readerAt
  have activeRows:=GeneralBorrowFreshActiveWithin.active_on _ _ .Read start (start+amount) runtime.formed.well active
  obtain ⟨done,shape,afterRows,well,ranges,capacity⟩:=S05CurrentReleaseIterator.release role.backing.allocation.extra current.protectedTags
    readerNode.tag reader readerNode readerAt hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨lower,upper,sameKind⟩:=activeRows position valid state stored accessed kind associated
      have kindEq:=sameKind rfl
      subst kind
      have rowPositive:=(GeneralRangeMapGeometry.facts role.backing.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
      have point : ∃byte,Window role.backing.id offset length byte ∧
          role.backing.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 ∧byte.2<role.backing.allocation.extra.locations.entries[position].range.stop.toNat:=by
        by_cases earlier : start.toNat≤role.backing.allocation.extra.locations.entries[position].range.start.toNat
        · exact ⟨(role.backing.id,role.backing.allocation.extra.locations.entries[position].range.start.toNat),⟨rfl,by omega,by omega⟩,Nat.le_refl _,rowPositive⟩
        · exact ⟨(role.backing.id,start.toNat),⟨rfl,by omega,by omega⟩,by omega,upper⟩
      obtain ⟨byte,inside,low,high⟩:=point
      have member : role.backing.allocation.extra.locations.entries[position]∈role.backing.allocation.extra.locations.entries.toList:=Array.mem_toList_iff.mpr (Array.getElem_mem valid)
      obtain ⟨cap⟩:=readable position valid positive lower upper
      have result:=row_read role exclusive current runtime distinct short parentTag parent reader readerNode concrete tagged readerAt
        temporary temporaryNode temporaryAt readerEdge temporaryEdge hidden temporaryHidden temporaryUnheld futureEq _ member byte inside low high
        ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩ cap
        .SkipChildrenOfAccessed role.backing.allocation.extra.locations.entries[position].range
      exact ⟨result.1,result.2.1,_,member,rfl,result.2.2⟩)
  refine ⟨done,shape,?_,capacity,fun position valid=>(afterRows position valid).2⟩
  rw [shape]
  refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations role.backing.allocation.extra _ runtime.formed.toGraphState,well⟩,?_⟩,
    ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
  · intro position valid;exact ⟨(afterRows position valid).1.2.1.present,(afterRows position valid).1.2.1.vacant⟩
  · intro position valid;exact (afterRows position valid).1.1
  · intro position valid;exact (afterRows position valid).1.2.2

end
end DuplicatePrefix.CurrentCallSpatialLenRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialLenRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Len release dependency {dependency}"
