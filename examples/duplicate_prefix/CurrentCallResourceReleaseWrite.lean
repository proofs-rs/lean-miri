import duplicate_prefix.CurrentCallResourceFinalWrite
import duplicate_prefix.CurrentCallAllocationLicense
namespace DuplicatePrefix.CurrentCallResourceReleaseWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
/-- Transport a real original pointer license through the actual locations-only
release, without requiring an initial live ownership window. -/
theorem completed_pointer {id offset before current allocation completion post place} (next : MachineHooks.BorrowState)
    (original : PointerInstance) (originalId : original.allocation=id)
    (oldIssued : SpatialDelegation before current id allocation completion original.grant)
    (oldBinding : PointerBinds allocation original)
    (physical : CurrentCallBoolScalarWrite.Window post place)
    (sameId : physical.id=id) (sameOffset : physical.offset.toNat=offset) (samePointer : physical.pointer=original.value)
    (rootTag : next.global.rootTag? id=current.global.rootTag? id)
    (length : physical.entry.allocation.len=allocation.len)
    (bytes : physical.entry.allocation.byteSize=allocation.byteSize)
    (shape : physical.entry.allocation.extra={allocation.extra with locations:=physical.entry.allocation.extra.locations})
    (capacity : physical.entry.allocation.extra.locations.size=allocation.extra.locations.size)
    (parents : ParentInterpretation physical.entry.allocation.extra completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra next.global)
    (distinct : physical.entry.allocation.extra.roots.toList.Nodup)
    (short : physical.entry.allocation.extra.nodes.size<65536)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority physical.entry.allocation.extra completion next.global.protectedTags original.grant)
      physical.offset (physical.offset+1) physical.entry.allocation.extra.locations) :
    (physical.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra physical.pointer.provenance)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  have live : post.memory.live.find? (fun row=>row.1==id)=some (id,physical.entry) := by simpa only [sameId] using physical.live
  have present : Present (ActualWorld post) id physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have issued:=CurrentCallAllocationLicense.spatial oldIssued post next physical.entry.allocation present rootTag length bytes capacity
    (by intro position root found;rw [shape];exact found)
    (by
      intro index node found
      exact ⟨node,by rw [shape];exact found,rfl,rfl,rfl,rfl⟩)
    completion (by intro root origin edge;exact edge)
  have binding : PointerBinds physical.entry.allocation original := by
    obtain ⟨node,nodeAt,mapped,provenance⟩:=oldBinding
    exact ⟨node,by rw [shape];exact nodeAt,by rw [shape];exact mapped,provenance⟩
  exact CurrentCallResourceFinalWrite.completed_pointer original originalId physical sameId sameOffset samePointer completion binding issued parents runtime distinct short owned
/-- Backward-compatible uniform-window interface. -/
theorem completed {initial oldTracker data owner id offset before current allocation completion post place} (next : MachineHooks.BorrowState)
    (original : UniformWindow initial oldTracker data owner id offset 1 .ret)
    (oldIssued : SpatialDelegation before current id allocation completion original.pointer.grant)
    (oldBinding : PointerBinds allocation original.pointer)
    (physical : CurrentCallBoolScalarWrite.Window post place)
    (sameId : physical.id=id) (sameOffset : physical.offset.toNat=offset) (samePointer : physical.pointer=original.pointer.value)
    (rootTag : next.global.rootTag? id=current.global.rootTag? id)
    (length : physical.entry.allocation.len=allocation.len)
    (bytes : physical.entry.allocation.byteSize=allocation.byteSize)
    (shape : physical.entry.allocation.extra={allocation.extra with locations:=physical.entry.allocation.extra.locations})
    (capacity : physical.entry.allocation.extra.locations.size=allocation.extra.locations.size)
    (parents : ParentInterpretation physical.entry.allocation.extra completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra next.global)
    (distinct : physical.entry.allocation.extra.roots.toList.Nodup)
    (short : physical.entry.allocation.extra.nodes.size<65536)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority physical.entry.allocation.extra completion next.global.protectedTags original.pointer.grant)
      physical.offset (physical.offset+1) physical.entry.allocation.extra.locations) :
    (physical.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra physical.pointer.provenance)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  exact completed_pointer next original.pointer original.pointerId oldIssued oldBinding physical sameId sameOffset samePointer rootTag length bytes shape capacity parents runtime distinct short owned

end
end DuplicatePrefix.CurrentCallResourceReleaseWrite
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceReleaseWrite" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual released original write dependency {dependency}"
