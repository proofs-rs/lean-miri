import duplicate_prefix.CurrentCallResourceRead
import duplicate_prefix.S05CurrentReleaseIterator

namespace DuplicatePrefix.CurrentCallResourceRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposureCardinality
open GeneralBorrowExposedNonleafPrimaryPath BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Actual mutable protector release uses the same normalized row geometry as
ordinary Write/Read. It needs neither full root attachment nor a leaf grant. -/
theorem release {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (concrete : ∃ suppliedId tag,W.pointer.value.provenance=.concrete suppliedId tag)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536)
    (node : TreeNode) (present : W.allocation.extra.nodes.get W.pointer.grant=some node)
    (hidden : node.isExposed=false) (start amount : UInt64)
    (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat)
    (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra W.pointer.grant .Write start (start+amount)) :
    let result:=W.allocation.extra.releaseProtector node.tag tracker.global.protectedTags
    result.status=.Released ∧ result.tree={W.allocation.extra with locations:=result.tree.locations} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree tracker.global ∧
      ParentInterpretation result.tree W.precise.completion ∧
      result.tree.locations.size=W.allocation.extra.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree W.precise.completion tracker.global.protectedTags W.pointer.grant)
        start (start+amount) result.tree.locations := by
  obtain ⟨G⟩:=geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) exclusive
  have witness (position : Nat) (valid : position<W.allocation.extra.locations.entries.size)
      (lower : W.allocation.extra.locations.entries[position].range.start.toNat<(start+amount).toNat)
      (upper : start.toNat<W.allocation.extra.locations.entries[position].range.stop.toNat) :
      ∃ byte : AllocId × Nat,Window id offset length byte ∧
        W.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 ∧
        byte.2<W.allocation.extra.locations.entries[position].range.stop.toNat := by
    have segmentPositive:=(GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
    by_cases earlier : start.toNat≤W.allocation.extra.locations.entries[position].range.start.toNat
    · exact ⟨(id,W.allocation.extra.locations.entries[position].range.start.toNat),⟨rfl,by omega,by omega⟩,Nat.le_refl _,segmentPositive⟩
    · exact ⟨(id,start.toNat),⟨rfl,by omega,by omega⟩,by omega,upper⟩
  let P:=fun (range : ByteRange) (location : LocationTree)=>
    LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location ∧
    (range.start.toNat<(start+amount).toNat→start.toNat<range.stop.toNat→
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant location)
  have rows : S05CurrentReleaseIterator.Rows P W.allocation.extra.locations := by
    intro position valid
    refine ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid,?_⟩
    intro lower upper
    obtain ⟨byte,inside,low,high⟩:=witness position valid lower upper
    exact CurrentCallResourceAccess.row_authority W exclusive byte inside _
      (Array.mem_toList_iff.mpr (Array.getElem_mem valid)) low high (runtime.formed.profile position valid) (runtime.possible position valid)
  have activeRows:=GeneralBorrowFreshActiveWithin.active_on _ _ .Write start (start+amount) runtime.formed.well active
  have mapped:=runtime.formed.allocator.nodeTags W.pointer.grant node present
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩:=S05CurrentReleaseIterator.release W.allocation.extra tracker.global.protectedTags
    node.tag W.pointer.grant node present hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨lower,upper,_⟩:=activeRows position valid state stored accessed kind associated
      obtain ⟨byte,inside,low,high⟩:=witness position valid lower upper
      have member : W.allocation.extra.locations.entries[position]∈W.allocation.extra.locations.entries.toList:=Array.mem_toList_iff.mpr (Array.getElem_mem valid)
      have current:=rows position valid
      cases kind with
      | Read =>
        have result:=CurrentCallResourceRead.concrete_read W G exclusive byte inside _ member low high concrete distinct current.1 short current.2.1 current.2.2.1
          .SkipChildrenOfAccessed W.allocation.extra.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun _ _=>result.2.2.2.2.2⟩
      | Write =>
        have result:=CurrentCallResourceAccess.concrete_write W G exclusive byte inside _ member low high concrete distinct current.1 short current.2.1 current.2.2.1
          .SkipChildrenOfAccessed W.allocation.extra.locations.entries[position].range
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,fun _ _=>result.2.2.2.2.2⟩)
  refine ⟨done,frame,?_,?_,capacity,?_⟩
  · rw [frame]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations W.allocation.extra _ runtime.formed.toGraphState,well⟩,?_⟩,
      ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid;exact ⟨(afterRows position valid).2.1.present,(afterRows position valid).2.1.vacant⟩
    · intro position valid;exact (afterRows position valid).1
    · intro position valid;exact (afterRows position valid).2.2.1
  · rw [frame]
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations W.allocation.extra _ W.parents.graph,W.parents.order,
      W.parents.dimension,W.parents.physical,W.parents.edgeLive,W.parents.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,older,rootSlot,rootAt,originAt,exposed,tag,path⟩:=W.parents.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,older,rootSlot,rootAt,originAt,exposed,tag,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before:={W.allocation.extra with locations:=(W.allocation.extra.releaseProtector node.tag tracker.global.protectedTags).tree.locations}) (after:=W.allocation.extra) rfl path⟩
  · rw [frame]
    intro position valid _ lower upper index currentNode currentPresent
    exact (afterRows position valid).2.2.2 lower upper index currentNode currentPresent

end
end DuplicatePrefix.CurrentCallResourceRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current resource release dependency {dependency}"
