import duplicate_prefix.CurrentCallResourceEntry
import duplicate_prefix.CurrentCallRootPhysicalWindow

namespace DuplicatePrefix.CurrentCallResourceRootPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

/-- The actual Bool clear retains precisely the physical prerequisites for the
ORIGINAL destination's final scalar store; post-clear full provenance WF and
initialization are not required. -/
theorem of_entry : ∃ window : CurrentCallBoolScalarWrite.Window out.finalMachine place,
    window.pointer=C.physical.pointer ∧ window.id=C.physical.id ∧ window.offset=C.physical.offset ∧
    CandidateCallBindings.WindowBinding out.finalMachine window.pointer window.id window.offset.toNat 1 := by
  let physical:=out.physical
  have mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra out.updated.extra)=.ok () out.updated := by
    simpa only [Allocation.setExtra,Allocation.mapExtra] using out.mutation
  obtain ⟨length,bytes,mutable,_,maskWF,maskLen,clear⟩:=CurrentCallBoolWindow.mutation_metadata physical out.updated.extra out.updated mutation
  have memory : out.finalMachine.memory.live=(out.sourceMachine.memory.live.filter (fun row=>row.1!=physical.id)).push
      (physical.id,{physical.entry with allocation:=out.updated}) := by
    rw [out.finalMachineEq]
    exact congrArg (fun memory=>memory.live) (MemoryCopyBridge.live_update_twice out.sourceMachine.memory physical.id
      {physical.entry with allocation:=physical.entry.allocation.setExtra out.boolOutput.child.tree} {physical.entry with allocation:=out.updated})
  have live : out.finalMachine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,{physical.entry with allocation:=out.updated}) := by
    rw [memory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have endpoint:=DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1 (by
    have bound:=physical.bounds
    have fits:=physical.capacity.toNat_lt
    simpa only [Size.ofBytes,UInt64.toNat_one] using (show physical.offset.toNat+1<2^64 by omega))
  have subset:=S04ReturnProvenanceClear.clear_pointer_subset physical.entry.allocation.provenanceMap out.updated.provenanceMap
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) _
    (AllocationCopy.snapshot (physical.entry.allocation.setExtra out.updated.extra)) endpoint clear
  have addresses : out.finalMachine.user.addresses=out.sourceMachine.user.addresses := by rw [out.finalMachineEq];rfl
  let window : CurrentCallBoolScalarWrite.Window out.finalMachine place:={
    pointer:=physical.pointer,physicalPointer:=physical.physicalPointer,layout:=physical.layout,aligned:=physical.aligned,
    id:=physical.id,entry:={physical.entry with allocation:=out.updated},base:=physical.base,offset:=physical.offset,capacity:=physical.capacity,
    live:=live,cachedBase:=by rw [addresses];exact physical.cachedBase,pointerAddress:=physical.pointerAddress,bounds:=physical.bounds,
    size:=bytes.trans physical.size,bytes:=length.trans physical.bytes,mutable:=mutable,maskValid:=maskWF,
    maskLength:=maskLen.trans (bytes.trans physical.size),pointerBounds:=by
      intro row member
      rw [length]
      exact ProvenanceCopy.WellFormed.pointerBounds physical.provenanceMap row (subset row member)}
  have sourceAddresses : out.sourceMachine.user.addresses=before.user.addresses := by rw [out.sourceMachineEq];rfl
  have sourceMemory : out.sourceMachine.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{out.sourceEntry with allocation:=out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}) := by rw [out.sourceMachineEq];rfl
  have sourceBinding:=CurrentCallBoolWindow.replace_binding before out.sourceMachine C.physical.pointer C.physical.id C.physical.offset.toNat 1
    C.returnBinding id out.sourceEntry {out.sourceEntry with allocation:=out.sourceEntry.allocation.setExtra out.sourceOutput.child.tree}
    out.sourceLive rfl rfl sourceAddresses sourceMemory
  have physicalBinding : CandidateCallBindings.WindowBinding out.sourceMachine physical.pointer physical.id physical.offset.toNat 1 := by
    simpa only [physical,out.physicalPointer,out.physicalId,out.physicalOffset] using sourceBinding
  have finalBinding:=CurrentCallBoolWindow.replace_binding out.sourceMachine out.finalMachine physical.pointer physical.id physical.offset.toNat 1
    physicalBinding physical.id physical.entry {physical.entry with allocation:=out.updated} physical.live length bytes addresses memory
  exact ⟨window,out.physicalPointer,out.physicalId,out.physicalOffset,finalBinding⟩

end
end DuplicatePrefix.CurrentCallResourceRootPhysical
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRootPhysical" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource root-physical dependency {dependency}"
