import duplicate_prefix.CurrentCallResourceCopyActivity
import duplicate_prefix.CurrentCallResourceCopyAccess
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
namespace DuplicatePrefix.CurrentCallResourceCopyBoolFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
private theorem window_owned {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (exclusive : demandOf mode = .exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (lo hi : UInt64) (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      lo hi W.allocation.extra.locations := by
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : W.allocation.extra.locations.entries[position] ∈ W.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  by_cases earlier : lo.toNat ≤ W.allocation.extra.locations.entries[position].range.start.toNat
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,W.allocation.extra.locations.entries[position].range.start.toNat)
      ⟨rfl,by omega,by omega⟩ _ member (Nat.le_refl _) segmentPositive
      (runtime.formed.profile position valid) (runtime.possible position valid)
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,lo.toNat) ⟨rfl,windowLower,by omega⟩ _ member (by omega) afterLower
      (runtime.formed.profile position valid) (runtime.possible position valid)


private theorem structure_frame {before after : BorrowTree} (nodes : after.nodes=before.nodes)
    (roots : after.roots=before.roots) (tags : after.tagMapping=before.tagMapping) :
    after={before with locations:=after.locations}:=by cases before;cases after;simp_all

private theorem normal_rows {before tracker data owner id offset length}
    (S : UniformWindow before tracker data owner id offset length .mut) (G : Geometry S)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts S.allocation.extra tracker.global)
    (kind : AccessKind) (lo hi : UInt64) (lower : offset≤lo.toNat) (upper : hi.toNat≤offset+length) :
    OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability S.allocation.extra location tracker.global.protectedTags S.pointer.grant kind))
      lo hi S.allocation.extra.locations:=by
  intro position valid positive beforeUpper afterLower
  have segmentPositive:=(GeneralRangeMapGeometry.facts S.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : S.allocation.extra.locations.entries[position]∈S.allocation.extra.locations.entries.toList:=Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  have obtainNormal : ∀ byte,Window id offset length byte→S.allocation.extra.locations.entries[position].range.start.toNat≤byte.2→byte.2<S.allocation.extra.locations.entries[position].range.stop.toNat→
      Nonempty (DuplicatePrefixNormalKind.Capability S.allocation.extra S.allocation.extra.locations.entries[position].data tracker.global.protectedTags S.pointer.grant kind):=by
    intro byte inside left right
    obtain ⟨normal⟩:=CurrentCallResourceAccess.selected_normal S G rfl byte inside _ member left right (runtime.formed.profile position valid) (runtime.possible position valid)
    exact ⟨DuplicatePrefixNormalKind.of_normal _ _ _ _ normal kind⟩
  by_cases earlier : lo.toNat≤S.allocation.extra.locations.entries[position].range.start.toNat
  · exact obtainNormal (id,S.allocation.extra.locations.entries[position].range.start.toNat) ⟨rfl,by omega,by omega⟩ (Nat.le_refl _) segmentPositive
  · exact obtainNormal (id,lo.toNat) ⟨rfl,lower,by omega⟩ (by omega) afterLower

/-- A quiet hidden Bool child retains its exact one-byte raw rights and activity
through the actual disjoint prefix Read and destination Write. -/
theorem same {before tracker sData sOwner bData bOwner id offset len boolOffset}
    (S : UniformWindow before tracker sData sOwner id offset.toNat len.toNat .mut)
    (B : UniformWindow before tracker bData bOwner id boolOffset 1 .ret)
    (allocation : B.allocation=S.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts S.allocation.extra tracker.global)
    (distinct : S.allocation.extra.roots.toList.Nodup) (short : S.allocation.extra.nodes.size<65536)
    (tag : BorTag) (concrete : S.pointer.value.provenance=.concrete id tag)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (entryAllocation : entry.allocation=S.allocation)
    (count : UInt64) (positive : (0 : UInt64)<count) (within : count≤len/2)
    (bounds : offset.toNat+len.toNat≤S.allocation.extra.locations.size.bytes.toNat)
    (boolStart : UInt64) (boolStartEq : boolStart.toNat=boolOffset)
    (boolNoWrap : (boolStart+1).toNat=boolStart.toNat+1)
    (separate : (offset+len).toNat≤boolStart.toNat ∨(boolStart+1).toNat≤offset.toNat)
    (node : TreeNode) (nodeAt : S.allocation.extra.nodes.get B.pointer.grant=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : B.pointer.grant≠S.pointer.grant)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin S.allocation.extra B.pointer.grant .Write boolStart (boolStart+1)) :
    let read:=S.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let write:=read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    OwnedOn (S05CompletedAncestryReadMutable.Authority write.tree B.precise.completion tracker.global.protectedTags B.pointer.grant)
      boolStart (boolStart+1) write.tree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin write.tree B.pointer.grant .Write boolStart (boolStart+1):=by
  let read:=S.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  have numeric:=PositiveRootCopyBounds.guarded len count offset S.allocation.extra.locations.size.bytes within bounds
  have fits : offset.toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt bounds S.allocation.extra.locations.size.bytes.toNat_lt
  have endEq : (offset+len).toNat=offset.toNat+len.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have middle : (offset+count).toNat=offset.toNat+count.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : offset.toNat+count.toNat<2^64)]
  have lastEq : (offset+count+count).toNat=offset.toNat+count.toNat+count.toNat:=by rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : (offset+count).toNat+count.toNat<2^64),middle]
  have spanPositive : offset.toNat<(offset+len).toNat:=by rw [endEq];have pos:=UInt64.lt_iff_toNat_lt.mp positive;simp only [UInt64.toNat_zero] at pos;omega
  obtain ⟨G⟩:=geometry_selected S (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) rfl
  have readFacts:=CurrentCallResourceRead.read_range_runtime S G rfl distinct short runtime (Size.ofBytes offset) (Size.ofBytes count) offset (offset+len)
    (Nat.le_refl _) (by omega) numeric.2.2.1 (Nat.le_refl _) (by change (offset+count).toNat≤_;omega) .VisitChildrenOfAccessed
  simp only [concrete] at readFacts
  have readRuntime : DuplicatePrefixBorrowContract.RuntimeFacts read.tree tracker.global:=readFacts.2.1
  have readFrame : read.tree={S.allocation.extra with locations:=read.tree.locations}:=
    structure_frame readFacts.2.2.2.2.1 readFacts.2.2.2.2.2.1 readFacts.2.2.2.2.2.2.1
  obtain ⟨readW,_,readPointer,readAllocation,readCompletion⟩:=CurrentCallResourceReleaseInstall.window S rfl entry live entryAllocation read.tree readFrame
    readRuntime readFacts.2.2.1 readFacts.2.2.2.2.2.2.2 offset len rfl rfl spanPositive endEq readFacts.2.2.2.1
  have readTree : readW.allocation.extra=read.tree:=by rw [readAllocation];rfl
  have readWRuntime : DuplicatePrefixBorrowContract.RuntimeFacts readW.allocation.extra tracker.global:=by rw [readTree];exact readRuntime
  obtain ⟨readG⟩:=geometry_selected readW (CandidateCurrentGrantRuntime.tree_rows _ _ readWRuntime) rfl
  have sourceBind:=S.binding
  obtain ⟨source,sourceAt,mapped,provenance⟩:=sourceBind
  rw [concrete] at provenance
  have tagged : S.allocation.extra.indexOfTag tag=some S.pointer.grant:=by rw [provenance.2];exact runtime.formed.allocator.nodeTags _ _ sourceAt
  have readActive:=CurrentCallResourceCopyActivity.concrete_of_normal S.allocation.extra tracker.global runtime tag S.pointer.grant B.pointer.grant source sourceAt offset count .Read numeric.2.2.1
    (normal_rows S G runtime .Read offset (offset+count) (Nat.le_refl _) (by omega)) tagged node nodeAt leaf hidden different boolStart (boolStart+1) active .VisitChildrenOfAccessed
  have writeBounds : (offset+count).toNat+count.toNat≤readW.allocation.extra.locations.size.bytes.toNat:=by rw [readTree,readFacts.2.2.2.2.2.2.2];omega
  have sourceAfter : readW.allocation.extra.nodes.get S.pointer.grant=some source:=by rw [readTree,readFacts.2.2.2.2.1];exact sourceAt
  have nodeAfter : readW.allocation.extra.nodes.get B.pointer.grant=some node:=by rw [readTree,readFacts.2.2.2.2.1];exact nodeAt
  have taggedAfter : readW.allocation.extra.indexOfTag tag=some S.pointer.grant:=by
    change readW.allocation.extra.tagMapping.get tag=some S.pointer.grant
    rw [readTree,readFacts.2.2.2.2.2.2.1]
    exact tagged
  have writeNormals:=normal_rows readW readG readWRuntime .Write (offset+count) (offset+count+count) (by omega) (by omega)
  simp only [readPointer] at writeNormals
  have writeActive:=CurrentCallResourceCopyActivity.concrete_of_normal readW.allocation.extra tracker.global readWRuntime tag S.pointer.grant B.pointer.grant source sourceAfter
    (offset+count) count .Write writeBounds writeNormals taggedAfter node nodeAfter leaf hidden different boolStart (boolStart+1) (by rw [readTree];exact readActive) .VisitChildrenOfAccessed
  have writeContract:=CurrentCallResourceAccess.write_range readW readG rfl (by rw [readTree,readFacts.2.2.2.2.2.1];exact distinct)
    (by rw [readTree,readFacts.2.2.2.2.1];exact short) readWRuntime.formed.well
    (fun cursor valid=>⟨readWRuntime.coherent cursor valid,readWRuntime.formed.profile cursor valid,readWRuntime.possible cursor valid⟩)
    (Size.ofBytes (offset+count)) (Size.ofBytes count) offset (offset+len) (Nat.le_refl _) (by omega) writeBounds
    (by change offset.toNat≤(offset+count).toNat;omega) (by change (offset+count+count).toNat≤_;omega) .VisitChildrenOfAccessed
  simp only [readTree,readPointer,concrete] at writeContract
  have oldOwned:=window_owned B rfl (by rw [allocation];exact runtime) boolStart (boolStart+1) (by omega) (by omega)
  have readOwned:=GeneralBorrowRangeOutsideOwned.owned _ S.allocation.extra (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    runtime.formed.well numeric.2.2.1 boolStart (boolStart+1) (by intro point lower upper;change point.toNat<offset.toNat ∨(offset+count).toNat≤point.toNat;omega) (by rw [←allocation];exact oldOwned)
  have writeOwned:=GeneralBorrowRangeOutsideOwned.owned _ read.tree (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    readRuntime.formed.well (by change (offset+count).toNat+count.toNat≤_;rw [readFacts.2.2.2.2.2.2.2];omega) boolStart (boolStart+1)
    (by intro point lower upper;change point.toNat<(offset+count).toNat ∨(offset+count+count).toNat≤point.toNat;omega) readOwned
  refine ⟨?_,?_⟩
  · intro position valid pos lower upper index found foundAt
    exact writeOwned position valid pos lower upper index found (by rw [allocation];rw [writeContract.nodes,readFacts.2.2.2.2.1] at foundAt;exact foundAt)
  · simpa only [readTree] using writeActive
end
end DuplicatePrefix.CurrentCallResourceCopyBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCopyBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual disjoint Bool copy dependency {dependency}"
