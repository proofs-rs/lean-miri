import duplicate_prefix.AllocationLifecycleFormation
namespace DuplicatePrefix.AllocationPointerFormation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open AllocationLifecycleFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Ready (allocation : Allocation Provenance Unit) (size : Size) : Prop :=
  allocation.byteSize=size ∧ allocation.len=allocation.byteSize.bytes.toNat ∧
  InitMaskCopy.WellFormed allocation.initializationMask ∧ allocation.initializationMask.len=allocation.byteSize ∧
  (∀ start finish,InitMaskCopy.InitializedOn allocation.initializationMask start finish) ∧
  ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len ∧ allocation.mutability=.Mut ∧ allocation.nativeBuffer=none

theorem backing (size : Size) (bytes : Array UInt8) (storage : Size→Align→Option (Array UInt8))
    (provided : storage size Align.ONE=some bytes) (length : bytes.size=size.bytes.toNat)
    (zero : ∀ i (h : i<bytes.size),bytes[i]=0) :
    ∃ allocation : Allocation Provenance Unit,
      Allocation.tryNew size Align.ONE .Zero storage=.ok allocation ∧ Ready allocation size := by
  obtain ⟨allocation,created,extra,len,sizeEq,mask,maskLength,initialized,provenance,mutable⟩ :=
    AllocationRootHookFormation.backing size bytes storage provided length zero
  obtain ⟨other,otherCreated,_,_,_,_,_,_,native⟩ :=
    AllocationStorageFormation.create (Prov:=Provenance) size .Zero bytes storage provided length zero
  have equal : allocation=other := Except.ok.inj (created.symm.trans otherCreated)
  subst other
  exact ⟨allocation,created,sizeEq,len,mask,maskLength,initialized,provenance,mutable,native⟩

/-- Actual allocate_ptr consumes the legal storage result, reserves its source
identity and installs initialized backing plus the real root tree/global. The
remaining address callback runs with that exact inserted state, and both its
success and failure outcomes are preserved. -/
theorem allocate {K U P : Type} [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (before : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (size : Size) (kind : MemoryKind K) (maximum : Size)
    (bytes : Array UInt8) (storage : Size→Align→Option (Array UInt8))
    (provided : storage size Align.ONE=some bytes) (length : bytes.size=size.bytes.toNat)
    (zero : ∀ i (h : i<bytes.size),bytes[i]=0)
    (adjustRoot : MemoryState Provenance BorrowTree K → MachineHooks.MachineState K U → AllocId → MemoryKind K →
      MemoryStateHookResult Provenance BorrowTree K (MachineHooks.MachineState K U) (Pointer Provenance))
    (emptyMemory : before.memory={}) (enabled : before.borrowTracker=some tracker)
    (initial : tracker.global=GlobalState.new) (race : before.dataRace=none)
    (noExtras : ((extras.get before.user).allocations.any (fun row=>row.1==AllocationLifecycleFormation.id))=false)
    (bounded : size.bytes≤maximum.bytes) :
    ∃ allocation : Allocation Provenance Unit,
      Ready allocation size ∧
      MemoryLifecycle.allocatePtr before.memory before synchronize size Align.ONE kind .Zero maximum none storage
        (initExtra extras) adjustRoot=
        finish (adjustRoot (inserted kind allocation)
          (synchronize (inserted kind allocation) (AllocationLifecycleFormation.initialized extras before tracker))
          AllocationLifecycleFormation.id kind) ∧
      (inserted kind allocation).live=#[
        (AllocationLifecycleFormation.id,⟨kind,allocation.withExtra (BorrowTree.new BorTag.one size)⟩)] ∧
      (AllocationLifecycleFormation.initialized extras before tracker).borrowTracker=
        some {tracker with global:=AllocationRootHookFormation.global AllocationLifecycleFormation.id} := by
  obtain ⟨allocation,created,ready⟩ := backing size bytes storage provided length zero
  have insertedExact := AllocationLifecycleFormation.insert extras before tracker allocation kind maximum adjustRoot
    emptyMemory enabled initial race noExtras (by rw [ready.1];exact bounded)
  refine ⟨allocation,ready,?_,?_,rfl⟩
  · unfold MemoryLifecycle.allocatePtr
    simp only [synchronize_self,created,Id.run,bind,pure]
    exact insertedExact
  · change #[(AllocationLifecycleFormation.id,(⟨kind,allocation.withExtra (BorrowTree.new BorTag.one allocation.byteSize)⟩ : LocalAllocation Provenance BorrowTree K))]=_
    rw [ready.1]
end DuplicatePrefix.AllocationPointerFormation
