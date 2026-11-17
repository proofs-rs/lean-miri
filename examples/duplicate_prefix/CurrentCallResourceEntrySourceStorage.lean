import duplicate_prefix.CurrentCallResourceSourceFinal
import duplicate_prefix.OrdinaryPhysicalValidity
import duplicate_prefix.S02SameDestinationUninitInitializedMutation
import duplicate_prefix.S02SameDestinationUninitInitializedBits
import duplicate_prefix.S02SameDestinationUninitProvenanceResult

namespace DuplicatePrefix.CurrentCallResourceEntrySourceStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Accepted-copy storage after the actual Bool clear. Existing pointer-byte
fragments are permitted; only the direct checks consumed by copy are retained. -/
structure Data (allocation : Allocation Provenance BorrowTree) (offset len : UInt64) : Prop where
  slice : DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len
  storage : allocation.len=allocation.byteSize.bytes.toNat
  provenance : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len
  mutable : allocation.mutability=.Mut
  storageFits : allocation.len+64<2^64

theorem Data.set_extra {allocation : Allocation Provenance BorrowTree} {offset len : UInt64}
    (data : Data allocation offset len) (tree : BorrowTree) : Data (allocation.setExtra tree) offset len :=
  ⟨data.slice,data.storage,data.provenance,data.mutable,data.storageFits⟩

private theorem initial {allocation : Allocation Provenance BorrowTree} {offset len : UInt64}
    (physical : OrdinaryPhysicalValidity.MutU8Slice allocation offset len)
    (room : allocation.len+64<2^64) : Data allocation offset len := by
  let valid:=physical.storage.provenance
  exact ⟨physical.slice_storage,physical.storage.byteLength,
    ⟨ProvenanceCopy.WellFormed.pointerOrder valid,ProvenanceCopy.WellFormed.pointerBounds valid,ProvenanceCopy.WellFormed.fragmentsAvoidPointers valid,by have count:=valid.fragment_count;omega⟩,
    physical.writable,room⟩

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

private theorem start_eq (_out : Output limits C count) : (UInt64.ofNat offset).toNat=offset := by
  have positive:=C.positive
  have last := (W.window (id,offset+len.toNat-1) ⟨rfl,by omega,by omega⟩).1
  have extent:=W.issued.capability.extent
  have bounded:=UInt64.toNat_lt W.allocation.byteSize.bytes
  have fits : offset<2^64 := by omega
  simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]

/-- The original initialized source window and explicit whole-allocation
backend margin supply the SAME live source row after actual entry. Nothing
is added to the entry conditions for zero-count or rejecting executions. -/
theorem of_entry
    (physical : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (room : W.allocation.len+64<2^64) :
    Data (CurrentCallResourceSourceFinal.entry out).allocation (UInt64.ofNat offset) len := by
  have source:=initial physical room
  by_cases same : out.physical.id=id
  · have beforeData : Data out.physical.entry.allocation (UInt64.ofNat offset) len := by
      rw [CurrentCallResourceSourceAfterBool.same_entry out same,out.sourceAllocation]
      exact source.set_extra out.sourceOutput.child.tree
    have mutation : Allocation.writeUninit (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        (out.physical.entry.allocation.setExtra out.updated.extra)=.ok () out.updated := by
      simpa only [Allocation.setExtra,Allocation.mapExtra] using out.mutation
    obtain ⟨expected,write,maskEq,length,bytes,mutable,extra,maskWF,maskLen,clear⟩:=
      S02SameDestinationUninitInitializedMutation.uninit (out.physical.entry.allocation.setExtra out.updated.extra)
        out.physical.capacity out.physical.offset out.physical.bytes out.physical.size out.physical.mutable
        out.physical.maskValid out.physical.maskLength out.physical.provenanceMap out.physical.bounds
    have equal : expected=out.updated:=(EStateM.Result.ok.inj (write.symm.trans mutation)).2
    subst expected
    change out.updated.len=out.physical.entry.allocation.len at length
    change out.updated.byteSize=out.physical.entry.allocation.byteSize at bytes
    change out.physical.entry.allocation.initializationMask.setRange
      (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) false=.ok out.updated.initializationMask at maskEq
    change out.updated.initializationMask.len=out.physical.entry.allocation.initializationMask.len at maskLen
    change ProvenanceMap.clear (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1))
      (AllocationCopy.snapshot (out.physical.entry.allocation.setExtra out.updated.extra)) (Size.ofBytes 8)
      out.physical.entry.allocation.provenanceMap=.ok () out.updated.provenanceMap at clear
    have fits : out.physical.offset.toNat+1<2^64:=Nat.lt_of_le_of_lt out.physical.bounds out.physical.capacity.toNat_lt
    have endNat : (out.physical.offset+1).toNat=out.physical.offset.toNat+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]
    have endpoint:=DuplicatePrefix.source_end (Size.ofBytes out.physical.offset) 1 (by simpa only [Size.ofBytes,UInt64.toNat_one] using fits)
    have fullFits : (UInt64.ofNat offset).toNat+len.toNat<2^64:=
      Nat.lt_of_le_of_lt beforeData.slice.bounds out.physical.entry.allocation.byteSize.bytes.toNat_lt
    have fullNat : (UInt64.ofNat offset+len).toNat=offset+len.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits,start_eq out]
    have separate : offset+len.toNat≤out.physical.offset.toNat ∨ out.physical.offset.toNat+1≤offset := by
      by_cases left : offset+len.toNat≤out.physical.offset.toNat
      · exact Or.inl left
      apply Or.inr
      by_cases right : out.physical.offset.toNat+1≤offset
      · exact right
      apply False.elim
      let point:=max offset out.physical.offset.toNat
      exact C.separate (out.physicalId.symm.trans same) (id,point)
        ⟨rfl,by dsimp [point];omega,by dsimp [point];have positive:=C.positive;omega⟩
        ⟨(out.physicalId.symm.trans same).symm,by rw [←out.physicalOffset];dsimp [point];omega,
          by rw [←out.physicalOffset];dsimp [point];omega⟩
    obtain ⟨mask,maskOK,_,_,initialized⟩:=S02SameDestinationUninitInitializedBits.one_byte_frame
      out.physical.entry.allocation.initializationMask (Size.ofBytes (UInt64.ofNat offset))
      (Size.ofBytes (UInt64.ofNat offset+len)) (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1))
      (Size.ofBytes (out.physical.offset+1)) beforeData.slice.maskValid beforeData.slice.initialized
      (by simp only [Size.ofBytes,fullNat,start_eq out];have positive:=C.positive;omega)
      (by rw [beforeData.slice.maskLength];simp only [Size.ofBytes,fullNat];have bound:=beforeData.slice.bounds;rw [start_eq out] at bound;exact bound)
      endpoint (by simpa only [Size.ofBytes,allocRange] using endNat)
      (by rw [out.physical.maskLength];simpa only [Size.ofBytes,endNat] using out.physical.bounds)
      (by simpa only [Size.ofBytes,allocRange,fullNat,endNat,start_eq out] using separate)
    have maskSame : mask=out.updated.initializationMask:=Except.ok.inj (maskOK.symm.trans maskEq)
    have initializedActual : InitMaskCopy.InitializedOn out.updated.initializationMask
        (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes (UInt64.ofNat offset+len)) := by
      rw [←maskSame];exact initialized
    have snapshotLen : (AllocationCopy.snapshot (out.physical.entry.allocation.setExtra out.updated.extra)).size=out.physical.entry.allocation.len := by
      cases out.physical.entry.allocation
      simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
        Allocation.setExtra,Allocation.mapExtra,Pure.pure,Except.pure,Except.toOption,Option.getD]
    have direct:=S02SameDestinationUninitProvenanceResult.after_clear out.physical.entry.allocation.provenanceMap out.updated.provenanceMap
      (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) _
      (AllocationCopy.snapshot (out.physical.entry.allocation.setExtra out.updated.extra))
      (by rw [snapshotLen];exact out.physical.provenanceMap) (by change (1 : UInt64)≠0;decide) endpoint
      (by rw [snapshotLen,out.physical.bytes];exact out.physical.capacity.toNat_lt) clear
    rw [snapshotLen,←length] at direct
    have result : Data out.updated (UInt64.ofNat offset) len := by
      refine ⟨⟨beforeData.slice.positive,beforeData.slice.signedSize,?_,maskWF,?_,initializedActual⟩,?_,direct,mutable,?_⟩
      · rw [bytes];exact beforeData.slice.bounds
      · rw [maskLen,bytes];exact beforeData.slice.maskLength
      · rw [length,bytes];exact beforeData.storage
      · rw [length];exact beforeData.storageFits
    simpa only [CurrentCallResourceSourceFinal.entry,ite_eq_left same] using result
  · have result:=source.set_extra out.sourceOutput.child.tree
    simpa only [CurrentCallResourceSourceFinal.entry,ite_eq_right same,out.sourceAllocation] using result

end
end DuplicatePrefix.CurrentCallResourceEntrySourceStorage
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceEntrySourceStorage" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual source storage dependency {dependency}"
