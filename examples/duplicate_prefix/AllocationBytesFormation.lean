import duplicate_prefix.AllocationStorageFormation
namespace DuplicatePrefix.AllocationBytesFormation
open Miri.ABI Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual byte-backed allocation creation admits arbitrary initialized data.
Only the raw byte count's representability is required; this is backing
construction, not ID reservation, address assignment or caller formation. -/
theorem create (bytes : Array UInt8) (mutability : Mutability)
    (fits : bytes.size<18446744073709551616) :
    ∃ allocation : Allocation Prov Unit,
      Allocation.fromBytes bytes Align.ONE mutability=.ok allocation ∧
      allocation.len=bytes.size ∧
      allocation.byteSize=Size.ofBytes (UInt64.ofNat bytes.size) ∧
      allocation.provenanceMap=ProvenanceMap.new ∧
      allocation.initializationMask=InitMask.new allocation.byteSize true ∧
      allocation.mutability=mutability ∧ allocation.align=Align.ONE ∧
      allocation.nativeBuffer=none := by
  have checked : AllocationStorageFormation.checkedAlign Align.ONE=.ok Align.ONE := by decide
  unfold AllocationStorageFormation.checkedAlign at checked
  have length : (UInt64.ofNat bytes.size).toNat=bytes.size := UInt64.toNat_ofNat_of_lt fits
  have bound : ¬ bytes.size>18446744073709551615 := by omega
  unfold Allocation.fromBytes
  unfold_internal ".Memory.sizeForArray"
  unfold_internal ".Memory.maxU64Nat"
  simp only [checked,bind,pure,Except.bind,Except.pure,bound,↓reduceIte,
    Size.ofBytes,length,beq_self_eq_true]
  exact ⟨_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Arbitrary bytes supplied by the actual source constructor satisfy the
storage, initialization and provenance invariants used by copy safety. -/
theorem initialized (bytes : Array UInt8) (mutability : Mutability)
    (fits : bytes.size<18446744073709551616) :
    ∃ allocation : Allocation Prov Unit,
      Allocation.fromBytes bytes Align.ONE mutability=.ok allocation ∧
      allocation.len=bytes.size ∧ allocation.len=allocation.byteSize.bytes.toNat ∧
      InitMaskCopy.WellFormed allocation.initializationMask ∧
      allocation.initializationMask.len=allocation.byteSize ∧
      (∀ start finish,InitMaskCopy.InitializedOn allocation.initializationMask start finish) ∧
      ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len ∧
      allocation.mutability=mutability := by
  obtain ⟨allocation,created,len,sizeEq,provenance,mask,mutable,_,_⟩ :=
    create (Prov:=Prov) bytes mutability fits
  refine ⟨allocation,created,len,?_,?_,?_,?_,?_,mutable⟩
  · rw [len,sizeEq];exact (UInt64.toNat_ofNat_of_lt fits).symm
  · rw [mask];exact True.intro
  · rw [mask];rfl
  · intro start finish;rw [mask];rfl
  · rw [provenance]
    constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
end DuplicatePrefix.AllocationBytesFormation
