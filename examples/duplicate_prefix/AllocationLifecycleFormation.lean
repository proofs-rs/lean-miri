import duplicate_prefix.AllocationRootHookFormation
namespace DuplicatePrefix.AllocationLifecycleFormation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def id : AllocId := ⟨1,by decide⟩
def reservedMemory : MemoryState Provenance BorrowTree K :=
  (({} : MemoryState Provenance BorrowTree K).reserveAllocId).1

theorem reserve : ({} : MemoryState Provenance BorrowTree K).reserveAllocId=
    (reservedMemory,.ok id) := by
  apply Prod.ext
  · rfl
  · change (({} : MemoryState Provenance BorrowTree K).reserveAllocId).2=.ok id
    unfold MemoryState.reserveAllocId
    unfold_internal ".MemoryState.containsId"
    simp [AllocId.ofUInt64,id,KeyedArray.contains,KeyedArray.empty]

theorem reserved_live : (reservedMemory (K:=K)).live=#[] := by
  unfold reservedMemory MemoryState.reserveAllocId
  unfold_internal ".MemoryState.containsId"
  simp [AllocId.ofUInt64,KeyedArray.contains,KeyedArray.empty]

def synchronize (memory : MemoryState Provenance BorrowTree K) (machine : MachineHooks.MachineState K U) :=
  {machine with memory}
@[simp] theorem synchronize_self (machine : MachineHooks.MachineState K U) : synchronize machine.memory machine=machine := by
  cases machine;rfl

def initExtra [DecidableEq K] (extras : MemoryExtras.Hooks K U P)
    (memory : MemoryState Provenance BorrowTree K) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (_ : MemoryKind K) (size : Size) (align : Align) :
    MemoryStateHookResult Provenance BorrowTree K (MachineHooks.MachineState K U) BorrowTree :=
  match PlaceMachine.initStackExtra (fun id _ _=>MemoryExtras.initAllocation extras id false) id size align
      (synchronize memory machine) with
  | .ok tree next => ⟨next.memory,next,.ok tree⟩
  | .error error next => ⟨next.memory,next,.error (reprStr error)⟩

def initialized (extras : MemoryExtras.Hooks K U P) (before : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) : MachineHooks.MachineState K U :=
  MemoryExtras.putAllocation extras (AllocationRootHookFormation.rooted (synchronize reservedMemory before) tracker id) id ⟨none,#[]⟩

def inserted (kind : MemoryKind K) (allocation : Allocation Provenance Unit) : MemoryState Provenance BorrowTree K :=
  {(reservedMemory (K:=K)) with live:=#[(id,⟨kind,allocation.withExtra (BorrowTree.new BorTag.one allocation.byteSize)⟩)]}

open Lean Elab in
elab "allocation_source_insert_live" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".MemoryState.insertLive" then some name else none
  let [name] := names | throwError "expected pinned allocation live insertion"
  Lean.Meta.mkConstWithFreshMVarLevels name

theorem inserted_exact (kind : MemoryKind K) (allocation : Allocation Provenance Unit) :
    allocation_source_insert_live (reservedMemory (K:=K)) id
      (⟨kind,allocation.withExtra (BorrowTree.new BorTag.one allocation.byteSize)⟩ : LocalAllocation Provenance BorrowTree K)=
      inserted kind allocation := by
  unfold_internal ".MemoryState.insertLive"
  rw [reserved_live]
  rfl

theorem synchronize_override (first second : MemoryState Provenance BorrowTree K)
    (machine : MachineHooks.MachineState K U) : synchronize first (synchronize second machine)=synchronize first machine := rfl

def finish (root : MemoryStateHookResult Provenance BorrowTree K (MachineHooks.MachineState K U) (Pointer Provenance)) :
    MemoryLifecycleResult Provenance BorrowTree K (MachineHooks.MachineState K U) (Pointer Provenance) :=
  match root.outcome with
  | .error message => ⟨root.memory,synchronize root.memory root.state,.error (.hookFailure "adjustAllocRootPointer" message)⟩
  | .ok pointer => ⟨root.memory,synchronize root.memory root.state,.ok pointer⟩

/-- The actual insertion prefix reserves ID one, executes the real machine
initializer, and installs backing/tree/global before invoking the explicit
root-address callback. Its outcome is executed and retained, never assumed. -/
theorem insert {K U P : Type} [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (before : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (allocation : Allocation Provenance Unit) (kind : MemoryKind K)
    (maximum : Size)
    (adjustRoot : MemoryState Provenance BorrowTree K → MachineHooks.MachineState K U → AllocId → MemoryKind K →
      MemoryStateHookResult Provenance BorrowTree K (MachineHooks.MachineState K U) (Pointer Provenance))
    (emptyMemory : before.memory={}) (enabled : before.borrowTracker=some tracker)
    (initial : tracker.global=GlobalState.new) (race : before.dataRace=none)
    (noExtras : ((extras.get before.user).allocations.any (fun row=>row.1==id))=false)
    (bounded : allocation.byteSize.bytes≤maximum.bytes) :
    MemoryLifecycle.insertAllocation before.memory before synchronize allocation kind maximum none
      (initExtra extras) adjustRoot=
      finish (adjustRoot (inserted kind allocation)
        (synchronize (inserted kind allocation) (initialized extras before tracker)) id kind) := by
  have hook := AllocationRootHookFormation.init_extra extras (synchronize reservedMemory before) tracker id allocation.byteSize allocation.align
    enabled initial race noExtras
  have bridge : initExtra extras reservedMemory (synchronize reservedMemory (synchronize {} before)) id kind allocation.byteSize allocation.align=
      ⟨reservedMemory,initialized extras before tracker,.ok (BorrowTree.new BorTag.one allocation.byteSize)⟩ := by
    unfold initExtra
    change (match PlaceMachine.initStackExtra (fun id _ _=>MemoryExtras.initAllocation extras id false) id allocation.byteSize allocation.align (synchronize reservedMemory before) with
      | .ok tree next => (⟨next.memory,next,.ok tree⟩ : MemoryStateHookResult Provenance BorrowTree K (MachineHooks.MachineState K U) BorrowTree)
      | .error error next => ⟨next.memory,next,.error (reprStr error)⟩)=_
    rw [hook]
    rfl
  have notLarge : ¬allocation.byteSize.bytes>maximum.bytes := by
    have b:=UInt64.le_iff_toNat_le.mp bounded
    intro greater
    have g:=UInt64.lt_iff_toNat_lt.mp greater
    omega
  unfold MemoryLifecycle.insertAllocation
  simp only [notLarge,↓reduceIte,emptyMemory,reserve,Id.run,bind,pure]
  unfold_internal ".MemoryLifecycle.insertAllocationWithId"
  simp only [Id.run,bind,pure,reduceCtorEq,↓reduceIte,bridge]
  rw [inserted_exact]
  simp only [synchronize_override]
  cases outcome : (adjustRoot (inserted kind allocation)
    (synchronize (inserted kind allocation) (initialized extras before tracker)) id kind).outcome <;>
    simp only [finish,outcome]
end DuplicatePrefix.AllocationLifecycleFormation
