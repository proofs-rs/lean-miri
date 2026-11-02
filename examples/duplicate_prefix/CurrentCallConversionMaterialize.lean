import duplicate_prefix.GlobalDataOnlyMaterialize
import duplicate_prefix.GlobalDataOnlyActualBytes
import duplicate_prefix.CurrentCallConversionChoiceProtocol
import duplicate_prefix.GlobalAddressLiveSizeFormation
/-! Actual finite-conversion composition through allocation-extra initialization
and lazy CURRENT memory/internal-static materialization. The internal conversion
equation is supplied by the finite converter proof, never by OrdinaryInput.
Every result retains the ACTUAL converter post-machine (including its caches,
addresses, counters and tape), and the existing stack is preserved by ensure.
Metadata/protocol frames permit the same initial choice tail after insertion. -/
namespace DuplicatePrefix.CurrentCallConversionMaterialize
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem adjust {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (pointer : Pointer CtfeProvenance → GlobalAllocationMachine.M K U (Pointer Provenance))
    (before after : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (conversion : Allocation.adjustFromTcx source target
      (fun _ _ state=>.ok (AllocationCopy.snapshot source) state) pointer before=.ok converted after)
    (enabled : after.borrowTracker=some tracker)
    (rootCached : tracker.global.rootTag? id=some root) (race : after.dataRace=none)
    (noExtras : ((extras.get after.user).allocations.any (fun row=>row.1==id))=false) :
    GlobalAllocationMachine.adjust target extras (GlobalDataOnlyAdjust.leaves pointer) id source before=
      .ok (.owned (converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)))
        (MemoryExtras.putAllocation extras after id ⟨none,#[]⟩) := by
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len=.ok (AllocationCopy.snapshot source) := by
    cases source
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]
  have init:=GlobalDataOnlyExtra.init_extra extras after tracker id root converted.byteSize converted.align enabled rootCached race noExtras
  simp only [GlobalAllocationMachine.adjust,GlobalDataOnlyAdjust.leaves,GlobalAllocationMachine.managedBytes,
    inspect,conversion,GlobalAllocationMachine.init,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
  simp only [pure,Pure.pure] at init
  rw [init]
/-- Actual managed compiler bytes use the same converter, including its
changed tracker, addresses and tape. Only the initial native-path setting is
used before conversion; allocation-extra initialization uses ACTUAL after. -/
theorem adjust_actual {Os R P H D O Aff B Host C : Type}
    (compiler : Miri.Input.CompilerProviders.Prepared) (image : Miri.Input.AllocationImage.Imported)
    (extras : MemoryExtras.Hooks MiriMemoryKind (Miri.Input.EvalPointerSource.User Os R P H D O Aff B Host) P)
    (sourceLeaves : Miri.Input.EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (address : MachineAddress.Hooks MiriMemoryKind (Miri.Input.EvalPointerSource.Control Os R P H D O Aff B Host))
    (pointer : Pointer CtfeProvenance→Miri.Input.EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance))
    (before after : Miri.Input.EvalPointerSource.Machine Os R P H D O Aff B Host)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (managed : (sourceLeaves.nativeLibraryPaths before.user.payload.payload.user.host).isEmpty=true)
    (conversion : Allocation.adjustFromTcx source compiler.runtime.target.base
      (fun _ _ state=>.ok (AllocationCopy.snapshot source) state) pointer before=.ok converted after)
    (enabled : after.borrowTracker=some tracker) (rootCached : tracker.global.rootTag? id=some root)
    (race : after.dataRace=none)
    (noExtras : ((extras.get after.user).allocations.any (fun row=>row.1==id))=false) :
    GlobalAllocationMachine.adjust compiler.runtime.target.base extras
      (GlobalDataOnlyActualBytes.leaves compiler image sourceLeaves address pointer) id source before=
      .ok (.owned (converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)))
        (MemoryExtras.putAllocation extras after id ⟨none,#[]⟩) := by
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len=.ok (AllocationCopy.snapshot source) := by
    cases source
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]
  have init:=GlobalDataOnlyExtra.init_extra extras after tracker id root converted.byteSize converted.align enabled rootCached race noExtras
  simp only [GlobalAllocationMachine.adjust,GlobalDataOnlyActualBytes.leaves,Miri.Input.EvalPointerSource.bytes,
    managed,inspect,conversion,GlobalAllocationMachine.init,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,ite_true]
  simp only [pure,Pure.pure] at init
  rw [init]

/-- The actual live insertion after allocation-extra initialization. It retains
all converter changes in the supplied machine, not the original machine. -/
def installed {K U : Type} (machine : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (allocation : Allocation Provenance BorrowTree) : MachineHooks.MachineState K U :=
  {machine with memory:={machine.memory with live:=
    (machine.memory.live.filter (fun row=>row.1!=id)).push (id,⟨.machine kind,allocation⟩)}}

theorem get_raw_memory {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P) (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K→PlaceMachine.AccessState K U→Nat→
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before after : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (descriptor : before.memory.findGlobal? id=some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjust : GlobalAllocationMachine.adjust target extras leaves id source before=.ok (.owned allocation) after) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer)=
        ⟨(installed after id kind allocation).memory,⟨installed after id kind allocation,none⟩,.ok allocation⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
  unfold_global_data ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjust]
  unfold_global_data ".Miri.Memory.MemoryState.insertLive"
  rfl

theorem get_raw_static {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P) (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K→PlaceMachine.AccessState K U→Nat→
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before after : MachineHooks.MachineState K U) (id : AllocId) (kind : K) (definition : Nat)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (descriptor : before.memory.findGlobal? id=some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (initial : initializer before.memory ⟨before,none⟩ definition=⟨before.memory,⟨before,none⟩,.ok source⟩)
    (adjust : GlobalAllocationMachine.adjust target extras leaves id source before=.ok (.owned allocation) after) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer)=
        ⟨(installed after id kind allocation).memory,⟨installed after id kind allocation,none⟩,.ok allocation⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,initial]
  unfold_global_data ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjust]
  unfold_global_data ".Miri.Memory.MemoryState.insertLive"
  rfl

theorem ensure_memory {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P) (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K→PlaceMachine.AccessState K U→Nat→
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (after : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.machine.memory.live.find? (fun row=>row.1==id)=none)
    (descriptor : before.machine.memory.findGlobal? id=some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjust : GlobalAllocationMachine.adjust target extras leaves id source before.machine=.ok (.owned allocation) after) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before=
      .ok () {before with machine:=installed after id kind allocation} := by
  have raw:=get_raw_memory target extras leaves initializer before.machine after id kind source allocation absent descriptor adjust
  simp only [GlobalAllocationMachine.ensure,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,raw]

theorem ensure_static {K U P : Type} [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P) (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K→PlaceMachine.AccessState K U→Nat→
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (after : MachineHooks.MachineState K U) (id : AllocId) (kind : K) (definition : Nat)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.machine.memory.live.find? (fun row=>row.1==id)=none)
    (descriptor : before.machine.memory.findGlobal? id=some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (initial : initializer before.machine.memory ⟨before.machine,none⟩ definition=⟨before.machine.memory,⟨before.machine,none⟩,.ok source⟩)
    (adjust : GlobalAllocationMachine.adjust target extras leaves id source before.machine=.ok (.owned allocation) after) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before=
      .ok () {before with machine:=installed after id kind allocation} := by
  have raw:=get_raw_static target extras leaves initializer before.machine after id kind definition source allocation absent descriptor initial adjust
  simp only [GlobalAllocationMachine.ensure,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,raw]

private theorem installed_here {K U : Type} (machine : MachineHooks.MachineState K U)
    (id : AllocId) (kind : K) (allocation : Allocation Provenance BorrowTree) :
    (installed machine id kind allocation).memory.live.find? (fun row=>row.1==id)=
      some (id,⟨.machine kind,allocation⟩) := by
  simp only [installed,Array.find?_push,Array.find?_filter,beq_self_eq_true,↓reduceIte]
  have noMatch : (fun row : AllocId×LocalAllocation Provenance BorrowTree K=>
      decide ((row.1!=id)=true ∧(row.1==id)=true))=(fun _=>false) := by
    funext row
    by_cases same : row.1=id <;> simp [same]
  rw [noMatch]
  have empty : machine.memory.live.find? (fun _=>false)=none := by
    apply Array.find?_eq_none.mpr
    simp
  rw [empty]
  rfl

/-- Installing the converted allocation preserves every metadata query when
its selected row has the same size/alignment/mutability as the real global.
This is the memory frame needed by the SAME initial address-protocol tail. -/
theorem metadata_frame {K U : Type} (machine : MachineHooks.MachineState K U)
    (id : AllocId) (kind : K) (allocation : Allocation Provenance BorrowTree)
    (known : machine.memory.getAllocInfo id=.ok
      ⟨allocation.byteSize,allocation.align,.liveData,allocation.mutability⟩) :
    ∀query,(installed machine id kind allocation).memory.getAllocInfo query=machine.memory.getAllocInfo query := by
  intro query
  by_cases same : query=id
  · subst query
    rw [known]
    simp only [MemoryState.getAllocInfo,installed_here]
    rfl
  · have other := GlobalAddressLiveSizeFormation.insert_lookup_other machine.memory id query
      (⟨.machine kind,allocation⟩ : LocalAllocation Provenance BorrowTree K) same
    change (installed machine id kind allocation).memory.live.find? (fun row=>row.1==query)=
      machine.memory.live.find? (fun row=>row.1==query) at other
    unfold MemoryState.getAllocInfo
    rw [other]
    rfl

/-- Materializing an already-live metadata ID preserves liveness for EVERY
ID. Other global/function/va-list lookup fields are definitionally unchanged. -/
theorem live_frame {K U : Type} (machine : MachineHooks.MachineState K U)
    (id : AllocId) (kind : K) (allocation : Allocation Provenance BorrowTree)
    (initial : machine.memory.isAllocLive id=true) :
    ∀query,(installed machine id kind allocation).memory.isAllocLive query=machine.memory.isAllocLive query := by
  intro query
  by_cases same : query=id
  · subst query
    rw [initial]
    simp [MemoryState.isAllocLive,installed]
  · have predicate : (fun row : AllocId×LocalAllocation Provenance BorrowTree K=>
        (row.1!=id) && (row.1==query))=(fun row=>row.1==query) := by
      funext row
      by_cases hit : row.1=query
      · simp [hit,same]
      · simp [hit]
    simp only [MemoryState.isAllocLive,installed,Array.any_push,Array.any_filter,predicate]
    have unequal : (id==query)=false := by simpa using Ne.symm same
    rw [unequal,Bool.or_false]

/-- The lower protocol depends on memory only through getAllocInfo. Its tail
therefore transports to the actual materialized memory with no new choice or
allocator-readiness premise. -/
theorem protocol_memory {K : Type} {before after : MemoryState Provenance BorrowTree K}
    (metadata : ∀id,after.getAllocInfo id=before.getAllocInfo id)
    (thread : AddressThreadId) {addresses final : GlobalAddressState} {tape finalTape : ExecutionChoices.Tape}
    {ids : List AllocId}
    (protocol : CurrentCallConversionChoiceProtocol.AddressProtocol before thread addresses tape ids final finalTape) :
    CurrentCallConversionChoiceProtocol.AddressProtocol after thread addresses tape ids final finalTape := by
  induction protocol with
  | nil addresses tape=>exact .nil addresses tape
  | cached addresses tape id rest base cached final afterTape tail ih=>
      exact .cached addresses tape id rest base cached final afterTape ih
  | typeId addresses tape id rest info uncached known kind final afterTape tail ih=>
      exact .typeId addresses tape id rest info uncached (by rw [metadata];exact known) kind final afterTape ih
  | managed addresses tape id rest info uncached known kind generation generationEq block final afterTape tail ih=>
      exact .managed addresses tape id rest info uncached (by rw [metadata];exact known) kind generation generationEq block final afterTape ih

end DuplicatePrefix.CurrentCallConversionMaterialize

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionMaterialize.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual conversion/materialization dependency {name}: {dependency}"
