import duplicate_prefix.CurrentCallResourceEntryRelease
import duplicate_prefix.CurrentCallResourceFinalWrite
import duplicate_prefix.CurrentCallAllocationLicense

namespace DuplicatePrefix.CurrentCallResourceReleasedWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

/-- Consume the internally derived root Plan's post-world resources for the
ORIGINAL destination. The temporary protected Bool pointer is not substituted. -/
theorem completed (released : CurrentCallResourceEntryRelease.Released out)
    (post : Before) (next : MachineHooks.BorrowState) (memory : post.memory=released.memory)
    (global : next.global=out.boolOutput.global.endCall (CurrentCallResourceEntryRelease.borrowFrame out))
    (physical : CurrentCallBoolScalarWrite.Window post place)
    (sameId : physical.id=out.physical.id) (sameOffset : physical.offset=out.physical.offset)
    (samePointer : physical.pointer=C.physical.pointer) :
    (physical.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra physical.pointer.provenance)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  have live : post.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,physical.entry):=by
    simpa only [sameId] using physical.live
  rw [memory] at live
  have entryEq:physical.entry={out.physical.entry with allocation:=out.updated.setExtra released.tree}:=
    (Prod.mk.inj (Option.some.inj (live.symm.trans released.live))).2
  have allocation : physical.entry.allocation=out.updated.setExtra released.tree:=congrArg LocalAllocation.allocation entryEq
  have present : Present (ActualWorld post) out.physical.id physical.entry.allocation:=by
    simp only [Present,ActualWorld,Array.toList_map]
    refine List.mem_map.mpr ⟨(out.physical.id,physical.entry),?_,rfl⟩
    rw [←memory] at live
    exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have rootTag : next.global.rootTag? out.physical.id=out.boolOutput.global.rootTag? out.physical.id:=by rw [global];rfl
  have capacity : physical.entry.allocation.extra.locations.size=out.updated.extra.locations.size:=by
    rw [allocation]
    exact released.capacity
  have metadata : ∀ index node,out.updated.extra.nodes.get index=some node→
      ∃ current,physical.entry.allocation.extra.nodes.get index=some current ∧ current.tag=node.tag ∧ current.parent=node.parent ∧
        current.isExposed=node.isExposed ∧ current.defaultInitialPermission=node.defaultInitialPermission:=by
    intro index node found
    refine ⟨node,?_,rfl,rfl,rfl,rfl⟩
    rw [allocation]
    change released.tree.nodes.get index=some node
    rw [released.shape]
    exact found
  have issued:=CurrentCallAllocationLicense.spatial (CurrentCallResourceBoolCurrent.parent_issued out) post next physical.entry.allocation present rootTag
    (by rw [allocation];rfl) (by rw [allocation];rfl) capacity
    (by intro position root found;rw [allocation];change released.tree.roots[position]?=some root;rw [released.shape];exact found)
    metadata (CurrentCallResourceBoolCurrent.completion out) (by intro root origin edge;exact edge)
  have binding : PointerBinds physical.entry.allocation C.V.pointer:=by
    obtain ⟨node,nodeAt,mapped,provenance⟩:=CurrentCallResourceBoolCurrent.parent_binding out
    refine ⟨node,?_,?_,provenance⟩
    · rw [allocation]
      change released.tree.nodes.get _=_
      rw [released.shape]
      exact nodeAt
    · rw [allocation]
      change released.tree.tagMapping.get _=_
      rw [released.shape]
      exact mapped
  apply CurrentCallResourceFinalWrite.completed C.V physical (sameId.trans out.physicalId)
    (congrArg UInt64.toNat (sameOffset.trans out.physicalOffset)) (samePointer.trans C.returnPointer)
    (CurrentCallResourceBoolCurrent.completion out) binding
  · simpa only [out.physicalId] using issued
  · rw [allocation]
    exact released.parents
  · rw [allocation,global]
    exact released.runtime
  · rw [allocation]
    exact released.distinct
  · rw [allocation]
    exact released.short
  · rw [allocation,sameOffset,global]
    exact released.owned

end
end DuplicatePrefix.CurrentCallResourceReleasedWrite
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceReleasedWrite" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved original released-write dependency {dependency}"
