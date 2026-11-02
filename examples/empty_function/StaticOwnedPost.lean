import empty_function.GlobalErrorAware
namespace EmptyFunction.StaticOwnedPost
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {K U P : Type}
theorem get_raw_owned [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before adjusted : MachineHooks.MachineState K U) (id : AllocId) (kind : K) (definition : Nat)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (evaluated : initializer before.memory ⟨before,none⟩ definition = ⟨before.memory,⟨before,none⟩,.ok source⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before = .ok (.owned allocation) adjusted) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer) =
        ⟨(GlobalErrorAware.installed adjusted id kind allocation).memory,⟨GlobalErrorAware.installed adjusted id kind allocation,none⟩,.ok allocation⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
  unfold_byte_source ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp [evaluated,adjustment]
  unfold_byte_source ".Miri.Memory.MemoryState.insertLive"
  simp [GlobalErrorAware.installed]

theorem ensure_owned [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (adjusted : MachineHooks.MachineState K U) (id : AllocId) (kind : K) (definition : Nat)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (evaluated : initializer before.machine.memory ⟨before.machine,none⟩ definition = ⟨before.machine.memory,⟨before.machine,none⟩,.ok source⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before.machine = .ok (.owned allocation) adjusted) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before =
      .ok () {before with machine := GlobalErrorAware.installed adjusted id kind allocation} := by
  have raw := get_raw_owned target extras leaves initializer before.machine adjusted id kind definition source allocation absent descriptor evaluated adjustment
  simp only [GlobalAllocationMachine.ensure,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,raw]

end EmptyFunction.StaticOwnedPost
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.StaticOwnedPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved static-owned axiom {dependency} in {name}"
