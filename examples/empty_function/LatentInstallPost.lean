import empty_function.LatentAdjustPost
namespace EmptyFunction.LatentInstallPost
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {K U P : Type}

/-- The source cache insertion keeps the actual adjusted machine state and
replaces only this allocation's live registry row. -/
def installed (machine : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (allocation : Allocation Provenance BorrowTree) : MachineHooks.MachineState K U :=
  {machine with memory := {machine.memory with live :=
    (machine.memory.live.filter fun row => row.1 != id).push (id,⟨.machine kind,allocation⟩)}}

/-- Internal composition boundary: a proved actual owned adjustment result
runs through getAllocRaw and its actual live insertion without losing nested
callback changes to memory, addresses, tags, choices or threads. -/
theorem get_raw [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before adjusted : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before = .ok (.owned allocation) adjusted) :
    MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some kind)
      (GlobalAllocationMachine.hooks target extras leaves initializer) =
        ⟨(installed adjusted id kind allocation).memory,⟨installed adjusted id kind allocation,none⟩,.ok allocation⟩ := by
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
  unfold_byte_source ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [adjustment]
  unfold_byte_source ".Miri.Memory.MemoryState.insertLive"
  rfl

theorem ensure [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U)
    (initializer : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K U → Nat →
      GlobalMemoryHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) (Allocation CtfeProvenance Unit))
    (before : MachineHooks.State K U) (adjusted : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (source : Allocation CtfeProvenance Unit) (allocation : Allocation Provenance BorrowTree)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (adjustment : GlobalAllocationMachine.adjust target extras leaves id source before.machine = .ok (.owned allocation) adjusted) :
    GlobalAllocationMachine.ensure kind (GlobalAllocationMachine.hooks target extras leaves initializer) id before =
      .ok () {before with machine := installed adjusted id kind allocation} := by
  have raw := get_raw target extras leaves initializer before.machine adjusted id kind source allocation absent descriptor adjustment
  simp only [GlobalAllocationMachine.ensure,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,raw]

/-- The owned source insertion establishes the exact current live row. -/
theorem live_row (machine : MachineHooks.MachineState K U) (id : AllocId) (kind : K)
    (allocation : Allocation Provenance BorrowTree) :
    (installed machine id kind allocation).memory.live.find? (fun row => row.1 == id) =
      some (id,⟨.machine kind,allocation⟩) := by
  have removed : (machine.memory.live.filter (fun row => row.1 != id)).find? (fun row => row.1 == id) = none := by
    apply Array.find?_eq_none.mpr
    intro row member same
    have notSame : (row.1 == id) = false := by
      simpa only [bne,Bool.not_eq_true'] using (Array.mem_filter.mp member).2
    rw [same] at notSame
    cases notSame
  simp only [installed,Array.find?_push,removed,beq_self_eq_true,↓reduceIte,Option.or]

/-- Registering a newly formed allocation preserves arbitrary existing live
trees. The new-tree fact is a pure constructor post, not operation success. -/
theorem world (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (kind : K) (allocation : Allocation Provenance BorrowTree)
    (prior : TreeRuntimeInput.World machine tracker)
    (formed : TreeRuntimeInput.TreeFormed allocation.extra tracker.global.nextPointerTag) :
    TreeRuntimeInput.World (installed machine id kind allocation) tracker := by
  refine ⟨prior.enabled,prior.globals,?_⟩
  intro row member
  change row ∈ (machine.memory.live.filter fun entry => entry.1 != id).push (id,⟨.machine kind,allocation⟩) at member
  rcases Array.mem_push.mp member with old | same
  · exact prior.liveTrees row (Array.mem_filter.mp old).1
  · subst row
    exact ⟨formed⟩
end EmptyFunction.LatentInstallPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LatentInstallPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent install post axiom {dependency} in {name}"
