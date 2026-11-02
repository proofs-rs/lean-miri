import Miri.Interpreter.GlobalAllocationMachine
import Lean

/-! Components of production lazy global materialization. These lemmas expose
initial lookup/registry data, rather than assuming that a memory operation
succeeds. General relocation conversion remains a separate obligation. -/
namespace EmptyFunction.LatentMaterialization
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
variable {K U P : Type}

/-- Managed, non-race global initialization registers exactly one empty
extras record and creates the actual new root tree. An already cached root is
used without consuming a new tag, independently of the rest of the memory. -/
theorem initExtra_cached_root [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (size : Size) (align : Align)
    (tracker : MachineHooks.BorrowState) (root : BorTag)
    (tracked : machine.borrowTracker=some tracker)
    (cached : tracker.global.rootTag? id=some root)
    (noRace : machine.dataRace=none)
    (vacant : (extras.get machine.user).allocations.any (fun row=>row.1==id)=false) :
    GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align machine =
      .ok (BorrowTree.new root size)
        (MemoryExtras.putAllocation extras machine id ⟨none,#[]⟩) := by
  have noentry : ¬ ∃ (i : Nat) (h : i < (extras.get machine.user).allocations.size),
      (extras.get machine.user).allocations[i].1=id := by
    simpa only [Array.any_eq_false, beq_iff_eq, not_exists] using vacant
  simp only [GlobalAllocationMachine.initExtra,tracked,GlobalState.rootPointerTag,cached,
    bind,EStateM.bind,pure,EStateM.pure,Except.pure,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    noRace,Option.map_none,Option.getD_none]
  simp [MemoryExtras.initAllocation,vacant,MemoryExtras.putAllocation,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,
    set,MonadStateOf.set,EStateM.set,tryCatchThe,tryCatch,MonadExceptOf.tryCatch,EStateM.tryCatch,
    Bind.bind,noRace,←tracked,noentry]

/-- A current live lookup makes production ensure an identity. All raw
compiler descriptors and unrelated allocations may remain arbitrary. -/
theorem ensure_live [DecidableEq K]
    (kind : K) (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : state.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id state =
      .ok () state := by
  simp [GlobalAllocationMachine.ensure,MemoryLifecycle.getAllocRaw,live,
    GlobalAllocationMachine.hooks,get,getThe,MonadStateOf.get,EStateM.get,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,EStateM.bind,pure,EStateM.pure,Id.run]

/-- Initializing only allocation extras preserves all physical memory and
current threads. Root-tag state is handled independently above. -/
theorem registered_memory (extras : MemoryExtras.Hooks K U P)
    (machine : MachineHooks.MachineState K U) (id : AllocId) :
    (MemoryExtras.putAllocation extras machine id ⟨none,#[]⟩).memory=machine.memory := rfl

theorem registered_threads (extras : MemoryExtras.Hooks K U P)
    (machine : MachineHooks.MachineState K U) (id : AllocId) :
    (MemoryExtras.putAllocation extras machine id ⟨none,#[]⟩).threads=machine.threads := rfl

/-- Raw snapshot used only to state byte preservation. -/
def snapshot {Prov Extra : Type} (allocation : Allocation Prov Extra) : Array UInt8 :=
  (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len).toOption.getD #[]

/-! Explicit data-only specialization. This does not cover relocated descriptors. -/
open Lean Elab Tactic in
elab "unfold_global_data " suffix:str : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := found | throwError "expected one source definition {suffix.getString}"
  evalTactic (← `(tactic| unfold $(mkIdent name)))

open Miri.ABI Miri.Memory Miri.Interpreter
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

set_option autoImplicit false in
structure DataOnlyFacts (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) : Prop where
  bytes : snapshot converted = snapshot source
  size : converted.byteSize = source.byteSize
  storage : converted.len = source.len
  mask : converted.initializationMask = source.initializationMask
  provenance : converted.provenanceMap = ProvenanceMap.new
  align : converted.align = source.align
  mutability : converted.mutability = source.mutability
  native : converted.nativeBuffer = none

theorem convert_data_only {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (target : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (state : State) (empty : source.provenanceMap = ProvenanceMap.new) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source target
        (fun _ _ current => .ok (snapshot source) current)
        pointer state = .ok converted state ∧ DataOnlyFacts source converted := by
  have emptyMap : ProvenanceMap.fromPresortedPtrs (#[] : Array (Size × Provenance)) = .ok ProvenanceMap.new := by
    simp only [ProvenanceMap.fromPresortedPtrs]
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    rfl
  cases source
  rename_i raw size provenance mask align mutability extra native
  change provenance = ProvenanceMap.new at empty
  subst provenance
  simp [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len, Allocation.adjustFromTcx, ProvenanceMap.new,
    emptyMap, List.forIn_nil,
    bind, Bind.bind, pure, Pure.pure, Except.pure, Id.run, Except.toOption]
  constructor <;> rfl


/-! Explicit data-only specialization. This does not cover relocated descriptors. -/
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def managedLeaves {K U : Type}
    (pointer : Pointer CtfeProvenance → GlobalAllocationMachine.M K U (Pointer Provenance)) :
    GlobalAllocationMachine.Leaves K U where
  bytes := GlobalAllocationMachine.managedBytes
  globalRootPointer := pointer
  diagnostic := fun _ _ _ => pure ()

theorem adjust_data_only {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (pointer : Pointer CtfeProvenance → GlobalAllocationMachine.M K U (Pointer Provenance))
    (before : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (empty : source.provenanceMap = ProvenanceMap.new)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == id)) = false) :
    ∃ converted : Allocation Provenance Unit,
      DataOnlyFacts source converted ∧
      GlobalAllocationMachine.adjust target extras (managedLeaves pointer) id source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation extras before id ⟨none,#[]⟩) := by
  obtain ⟨converted,conversion,facts⟩ := convert_data_only source target pointer before empty
  refine ⟨converted,facts,?_⟩
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
      .ok (snapshot source) := by
    cases source
    simp [snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len, pure, Pure.pure, Except.pure, Except.toOption]
  have init := initExtra_cached_root extras before id source.byteSize source.align tracker root
    enabled rootCached race noExtras
  simp only [GlobalAllocationMachine.adjust, managedLeaves, GlobalAllocationMachine.managedBytes,
    inspect, conversion, facts.size, facts.align, GlobalAllocationMachine.init,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]
  simp only [pure, Pure.pure] at init
  rw [init]

/-! Explicit data-only specialization. This does not cover relocated descriptors. -/
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def cached {K U P : Type} (extras : MemoryExtras.Hooks K U P)
    (before : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (allocation : Allocation Provenance BorrowTree) : MachineHooks.MachineState K U :=
  let after := MemoryExtras.putAllocation extras before id ⟨none,#[]⟩
  {after with memory := {before.memory with live :=
    (before.memory.live.filter fun old => old.1 != id).push (id,⟨.machine kind,allocation⟩)}}

theorem alloc_info {K U : Type} (before : MachineHooks.MachineState K U)
    (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (absent : (before.memory.live.find? (fun old => old.1 == id)) = none)
    (noFunction : before.memory.hasFunctionPointer id = false)
    (noVaList : before.memory.hasVaListId id = false)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    before.memory.getAllocInfo id =
      .ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
  unfold MemoryState.hasVaListId at noVaList
  simp [MemoryState.getAllocInfo,absent,noFunction,noVaList,descriptor,
    pure, Pure.pure, Except.pure]

theorem get_raw_data_only {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (pointer : Pointer CtfeProvenance → GlobalAllocationMachine.M K U (Pointer Provenance))
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (kind : K) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (empty : source.provenanceMap = ProvenanceMap.new)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == id)) = false)
    (absent : (before.memory.live.find? (fun old => old.1 == id)) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    ∃ converted : Allocation Provenance Unit,
      DataOnlyFacts source converted ∧
      let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
      MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
        (GlobalAllocationMachine.hooks target extras (managedLeaves pointer) initializer) =
          ⟨(cached extras before id kind allocation).memory,
            ⟨cached extras before id kind allocation,none⟩,.ok allocation⟩ := by
  obtain ⟨converted,facts,adjust⟩ := adjust_data_only target extras pointer before tracker
    id root source empty enabled rootCached race noExtras
  refine ⟨converted,facts,?_⟩
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks, Id.run, bind, Bind.bind, pure, Pure.pure]
  unfold_global_data ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjust]
  unfold_global_data ".Miri.Memory.MemoryState.insertLive"
  rfl
theorem ensure_data_only {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (pointer : Pointer CtfeProvenance → GlobalAllocationMachine.M K U (Pointer Provenance))
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (kind : K) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (empty : source.provenanceMap = ProvenanceMap.new)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.machine.dataRace = none)
    (noExtras : ((extras.get before.machine.user).allocations.any (fun row => row.1 == id)) = false)
    (absent : (before.machine.memory.live.find? (fun old => old.1 == id)) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    ∃ converted : Allocation Provenance Unit,
      DataOnlyFacts source converted ∧
      GlobalAllocationMachine.ensure kind
        (GlobalAllocationMachine.hooks target extras (managedLeaves pointer) initializer) id before =
        .ok () {before with machine := (cached extras before.machine id kind
          (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))} := by
  obtain ⟨converted,facts,raw⟩ := get_raw_data_only target extras pointer initializer before.machine tracker id kind root source
    empty enabled rootCached race noExtras absent descriptor
  refine ⟨converted,facts,?_⟩
  simp only [GlobalAllocationMachine.ensure, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, Pure.pure, EStateM.pure, raw]


end EmptyFunction.LatentMaterialization

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.LatentMaterialization." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function materialization axiom {dependency}"
