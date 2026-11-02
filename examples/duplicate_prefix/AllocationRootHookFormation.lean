import duplicate_prefix.AllocationStorageFormation
import Miri.Interpreter.MemoryExtras
namespace DuplicatePrefix.AllocationRootHookFormation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def tag2 : BorTag := ⟨2,by decide⟩
def global (id : AllocId) : GlobalState := {nextPointerTag:=tag2,rootPointerTags:=#[(id,BorTag.one)]}

theorem root (id : AllocId) : GlobalState.new.rootPointerTag id=.ok (global id,BorTag.one) := rfl

def rooted (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState) (id : AllocId) :=
  {machine with borrowTracker:=some {tracker with global:=global id}}

/-- The real allocation initializer allocates the first root tag, constructs
BorrowTree.new, and inserts the shared extras row. Initial table/clock facts
are inputs; no hook-success or post-allocation resource premise is supplied. -/
theorem init_extra {K U P : Type} [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P)
    (before : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (size : Size) (align : Align)
    (enabled : before.borrowTracker=some tracker) (initial : tracker.global=GlobalState.new)
    (race : before.dataRace=none)
    (noExtras : ((extras.get before.user).allocations.any (fun row=>row.1==id))=false) :
    PlaceMachine.initStackExtra (fun id _ _=>MemoryExtras.initAllocation extras id false) id size align before=
      .ok (BorrowTree.new BorTag.one size)
        (MemoryExtras.putAllocation extras (rooted before tracker id) id ⟨none,#[]⟩) := by
  have allocated : tracker.global.rootPointerTag id=.ok (global id,BorTag.one) := by rw [initial];exact root id
  simp only [PlaceMachine.initStackExtra,enabled,allocated,rooted,race,
    MemoryExtras.initAllocation,noExtras,MemoryExtras.putAllocation,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,EStateM.tryCatch,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,Bool.false_eq_true,ite_false]

/-- Storage facts survive the actual extra installation verbatim. -/
theorem backing (size : Size) (bytes : Array UInt8) (storage : Size→Align→Option (Array UInt8))
    (provided : storage size Align.ONE=some bytes) (length : bytes.size=size.bytes.toNat)
    (zero : ∀ i (h : i<bytes.size),bytes[i]=0) :
    ∃ allocation : Allocation Provenance Unit,
      Allocation.tryNew size Align.ONE .Zero storage=.ok allocation ∧
      let installed:=allocation.withExtra (BorrowTree.new BorTag.one size)
      installed.extra=BorrowTree.new BorTag.one size ∧ installed.len=installed.byteSize.bytes.toNat ∧
      installed.byteSize=size ∧ InitMaskCopy.WellFormed installed.initializationMask ∧
      installed.initializationMask.len=installed.byteSize ∧
      (∀ start finish,InitMaskCopy.InitializedOn installed.initializationMask start finish) ∧
      ProvenanceCopy.WellFormed installed.provenanceMap installed.len ∧ installed.mutability=.Mut := by
  obtain ⟨allocation,created,len,sizeEq,mask,length,initialized,provenance,mutable⟩ :=
    AllocationStorageFormation.initialized (Prov:=Provenance) size bytes storage provided length zero
  exact ⟨allocation,created,rfl,len,sizeEq,mask,length,initialized,provenance,mutable⟩
end DuplicatePrefix.AllocationRootHookFormation
