import duplicate_prefix.GlobalDataOnlyAdjust

/-! Known data-only compiler memory images materialize through get_alloc_raw,
including readonly images. The descriptor attributes agree with the CTFE image;
function and va-list precedence are ruled out explicitly. -/
namespace DuplicatePrefix.GlobalDataOnlyMaterialize
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

theorem get_raw {K U P : Type} [DecidableEq K]
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
      GlobalDataOnlyConversion.Facts source converted ∧
      let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
      MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
        (GlobalAllocationMachine.hooks target extras (GlobalDataOnlyAdjust.leaves pointer) initializer) =
          ⟨(cached extras before id kind allocation).memory,
            ⟨cached extras before id kind allocation,none⟩,.ok allocation⟩ := by
  obtain ⟨converted,facts,adjust⟩ := GlobalDataOnlyAdjust.adjust_exists target extras pointer before tracker
    id root source empty enabled rootCached race noExtras
  refine ⟨converted,facts,?_⟩
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks, Id.run, bind, Bind.bind, pure, Pure.pure]
  unfold_global_data ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjust, Id.run, bind, Bind.bind, pure, Pure.pure]
  unfold_global_data ".Miri.Memory.MemoryState.insertLive"
  rfl
theorem ensure {K U P : Type} [DecidableEq K]
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
      GlobalDataOnlyConversion.Facts source converted ∧
      GlobalAllocationMachine.ensure kind
        (GlobalAllocationMachine.hooks target extras (GlobalDataOnlyAdjust.leaves pointer) initializer) id before =
        .ok () {before with machine := (cached extras before.machine id kind
          (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))} := by
  obtain ⟨converted,facts,raw⟩ := get_raw target extras pointer initializer before.machine tracker id kind root source
    empty enabled rootCached race noExtras absent descriptor
  refine ⟨converted,facts,?_⟩
  simp only [GlobalAllocationMachine.ensure, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, Pure.pure, EStateM.pure, raw]

end DuplicatePrefix.GlobalDataOnlyMaterialize

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GlobalDataOnlyMaterialize.alloc_info,
      ``DuplicatePrefix.GlobalDataOnlyMaterialize.get_raw,
      ``DuplicatePrefix.GlobalDataOnlyMaterialize.ensure] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved global materialization dependency {dependency}"
