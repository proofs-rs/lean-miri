import duplicate_prefix.CurrentCallResourceRead
import duplicate_prefix.CurrentCallResourceReleaseInstall
import duplicate_prefix.PositiveRootCopyBounds
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
namespace DuplicatePrefix.CurrentCallResourceCopyAccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private abbrev RowRuntime (tree : BorrowTree) (flags : ProtectedTags) (location : LocationTree) :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location flags ∧
  GeneralBorrowLocationSifaConsistency.Profile tree location flags ∧GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location

private theorem runtime_after {tree : BorrowTree} {global : GlobalState} {rowPred : LocationTree→Prop}
    {frame : LocationTree→LocationTree→Prop} {lo hi : UInt64} {result : BorrowTree.BorrowTreeAccessResult}
    (old : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (contract : GeneralBorrowConcreteRangeInvariant.Contract tree rowPred (RowRuntime tree global.protectedTags) frame lo hi result) :
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global := by
  rw [contract.tree_eq]
  refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ old.formed.toGraphState,contract.well⟩,?_⟩,
    ?_,?_,⟨old.below.mapping,old.below.protectors⟩⟩
  · intro cursor valid
    exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
  · intro cursor valid
    exact (contract.runtime cursor valid).1
  · intro cursor valid
    exact (contract.runtime cursor valid).2.2

private theorem parents_after {tree : BorrowTree} {completion : Completion} {after : BorrowTree}
    (old : ParentInterpretation tree completion) (shape : after={tree with locations:=after.locations}) :
    ParentInterpretation after completion := by
  rw [shape]
  refine ⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ old.graph,old.order,old.dimension,old.physical,old.edgeLive,old.primaryNone,?_⟩
  intro position root slot origin edge
  obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩:=old.virtual position root slot origin edge
  exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before:={tree with locations:=after.locations}) (after:=tree) rfl path⟩

/-- The actual prefix Read then destination Write are derived from ONE current
raw family and optional parents. The intermediate view uses the literal read
row installation, not an updated allocation in the old world. -/
theorem run {before tracker data owner id offset len}
    (W : UniformWindow before tracker data owner id offset.toNat len.toNat .mut)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (allocation : entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size<65536)
    (tag : BorTag) (concrete : W.pointer.value.provenance=.concrete id tag)
    (count : UInt64) (positive : (0 : UInt64)<count) (within : count≤len/2)
    (bounds : offset.toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat) :
    let read:=W.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let write:=read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    read.status=.Completed ∧write.status=.Completed ∧DuplicatePrefixBorrowContract.RuntimeFacts write.tree tracker.global ∧
    ParentInterpretation write.tree W.precise.completion ∧write.tree={W.allocation.extra with locations:=write.tree.locations} ∧
    write.tree.locations.size=W.allocation.extra.locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority write.tree W.precise.completion tracker.global.protectedTags W.pointer.grant)
      offset (offset+len) write.tree.locations ∧
    (∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra target .Write offset (offset+len)→
      GeneralBorrowFreshActiveWithin.ActiveWithin write.tree target .Write offset (offset+len)) := by
  have numeric:=PositiveRootCopyBounds.guarded len count offset W.allocation.extra.locations.size.bytes within bounds
  have sumSmall : offset.toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt bounds W.allocation.extra.locations.size.bytes.toNat_lt
  have endEq : (offset+len).toNat=offset.toNat+len.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt sumSmall]
  have middleEq : (offset+count).toNat=offset.toNat+count.toNat:=by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : offset.toNat+count.toNat<2^64)]
  have finalEq : (offset+count+count).toNat=offset.toNat+count.toNat+count.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : (offset+count).toNat+count.toNat<2^64),middleEq]
  have spanPositive : offset.toNat<(offset+len).toNat:=by
    have pos:=UInt64.lt_iff_toNat_lt.mp positive
    simp only [UInt64.toNat_zero] at pos
    omega
  obtain ⟨G⟩:=geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) rfl
  have readContract:=CurrentCallResourceRead.read_range W G rfl distinct short runtime.formed.well
    (fun cursor valid=>⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid,runtime.possible cursor valid⟩)
    (Size.ofBytes offset) (Size.ofBytes count) offset (offset+len) (Nat.le_refl _) (by omega) numeric.2.2.1 (Nat.le_refl _) (by change (offset+count).toNat≤_;omega) .VisitChildrenOfAccessed
  simp only [concrete] at readContract
  let read:=W.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  have readRuntime : DuplicatePrefixBorrowContract.RuntimeFacts read.tree tracker.global:=runtime_after runtime readContract
  have readParents : ParentInterpretation read.tree W.precise.completion:=parents_after W.parents readContract.tree_eq
  have readOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority read.tree W.precise.completion tracker.global.protectedTags W.pointer.grant)
      offset (offset+len) read.tree.locations:=by
    intro cursor valid pos start stop index node present
    exact readContract.rows cursor valid pos start stop index node (by rw [←readContract.nodes];exact present)
  obtain ⟨current,_,pointerEq,allocationEq,preciseEq⟩:=CurrentCallResourceReleaseInstall.window W rfl entry live allocation read.tree
    readContract.tree_eq readRuntime readParents readContract.capacity offset len rfl rfl spanPositive endEq readOwned
  have treeEq : current.allocation.extra=read.tree:=by rw [allocationEq];rfl
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra tracker.global:=by rw [treeEq];exact readRuntime
  obtain ⟨currentGeometry⟩:=geometry_selected current (CandidateCurrentGrantRuntime.tree_rows _ _ currentRuntime) rfl
  have writeContract:=CurrentCallResourceAccess.write_range current currentGeometry rfl
    (by rw [treeEq,readContract.roots];exact distinct) (by rw [treeEq,readContract.nodes];exact short) currentRuntime.formed.well
    (fun cursor valid=>⟨currentRuntime.coherent cursor valid,currentRuntime.formed.profile cursor valid,currentRuntime.possible cursor valid⟩)
    (Size.ofBytes (offset+count)) (Size.ofBytes count) offset (offset+len) (Nat.le_refl _) (by omega)
    (by rw [treeEq,readContract.capacity];change (offset+count).toNat+count.toNat≤_;omega)
    (by change offset.toNat≤(offset+count).toNat;omega) (by change (offset+count+count).toNat≤_;omega) .VisitChildrenOfAccessed
  simp only [treeEq,pointerEq,concrete,preciseEq] at writeContract
  have writtenRuntime:=runtime_after readRuntime writeContract
  have writtenParents:=parents_after readParents writeContract.tree_eq
  let written:=read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  have shape : written.tree={W.allocation.extra with locations:=written.tree.locations}:=by
    calc
      written.tree={read.tree with locations:=written.tree.locations}:=writeContract.tree_eq
      _={W.allocation.extra with locations:=written.tree.locations}:=by rw [readContract.tree_eq]
  refine ⟨readContract.completed,writeContract.completed,writtenRuntime,writtenParents,shape,writeContract.capacity.trans readContract.capacity,?_,?_⟩
  · intro cursor valid pos start stop index node present
    exact writeContract.rows cursor valid pos start stop index node (by rw [←writeContract.nodes];exact present)
  · intro target active
    have afterRead:=GeneralBorrowFreshActiveWithinAccess.normal W.allocation.extra tag (Size.ofBytes offset) (Size.ofBytes count)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed target offset (offset+len) runtime.formed.well numeric.2.2.1
      (Nat.le_refl _) (by change (offset+count).toNat≤_;omega) active
    exact GeneralBorrowFreshActiveWithinAccess.normal read.tree tag (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed target offset (offset+len) readRuntime.formed.well
      (by change (offset+count).toNat+count.toNat≤_;rw [readContract.capacity];omega)
      (by change offset.toNat≤(offset+count).toNat;omega) (by change (offset+count+count).toNat≤_;omega) afterRead
end
end DuplicatePrefix.CurrentCallResourceCopyAccess
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCopyAccess" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current resource copy access dependency {dependency}"
