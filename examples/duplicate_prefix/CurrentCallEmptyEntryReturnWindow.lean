import duplicate_prefix.CurrentCallRootPhysicalWindow
namespace DuplicatePrefix.CurrentCallEmptyEntryReturnWindow
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual initial Bool clear and final tree-only release row supply the
physical scalar-store window. Previous initialization and post-clear full
provenance well-formedness are unnecessary. -/
theorem of_mutation {before final : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (tree released : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
      (Size.ofBytes 8) (physical.entry.allocation.setExtra tree)=.ok () updated)
    (live : final.memory.live.find? (fun row=>row.1==physical.id)=
      some (physical.id,{physical.entry with allocation:=updated.setExtra released}))
    (addresses : final.user.addresses=before.user.addresses)
    (binding : CandidateCallBindings.WindowBinding final physical.pointer physical.id physical.offset.toNat 1)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (extras : final.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras) :
    ∃ window : CurrentCallBoolScalarWrite.Window final place,
      window.pointer=physical.pointer ∧ window.id=physical.id ∧ window.offset=physical.offset ∧
      window.entry={physical.entry with allocation:=updated.setExtra released} ∧
      CandidateCallBindings.WindowBinding final window.pointer window.id window.offset.toNat 1 ∧
      CurrentCallBoolProtection.WindowReady final window.id window.offset.toNat 1 := by
  obtain ⟨length,bytes,mutable,extra,maskWF,maskLen,clear⟩ := CurrentCallBoolWindow.mutation_metadata physical tree updated mutation
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1 (by
    have fits := physical.capacity.toNat_lt
    have bounds := physical.bounds
    simpa only [Size.ofBytes,UInt64.toNat_one] using (show physical.offset.toNat+1<2^64 by omega))
  have subset := S04ReturnProvenanceClear.clear_pointer_subset physical.entry.allocation.provenanceMap updated.provenanceMap
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) _
    (AllocationCopy.snapshot (physical.entry.allocation.setExtra tree)) endpoint clear
  let window : CurrentCallBoolScalarWrite.Window final place := {
    pointer:=physical.pointer,physicalPointer:=physical.physicalPointer,layout:=physical.layout,aligned:=physical.aligned
    id:=physical.id,entry:={physical.entry with allocation:=updated.setExtra released},base:=physical.base,offset:=physical.offset,capacity:=physical.capacity
    live:=live,cachedBase:=by rw [addresses];exact physical.cachedBase
    pointerAddress:=physical.pointerAddress,bounds:=physical.bounds,size:=bytes.trans physical.size,bytes:=length.trans physical.bytes
    mutable:=mutable,maskValid:=maskWF,maskLength:=maskLen.trans (bytes.trans physical.size)
    pointerBounds:=by
      intro row member
      change row.1.bytes.toNat+8≤updated.len
      rw [length]
      exact ProvenanceCopy.WellFormed.pointerBounds physical.provenanceMap row (subset row member) }
  exact ⟨window,rfl,rfl,rfl,rfl,binding,ready.transport extras⟩

end DuplicatePrefix.CurrentCallEmptyEntryReturnWindow
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryReturnWindow" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty return window dependency {dependency}"
