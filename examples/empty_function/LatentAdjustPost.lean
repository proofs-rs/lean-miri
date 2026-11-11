import empty_function.RelocationRoot
import empty_function.RootTagPost
import empty_function.RelocationByteFold
namespace EmptyFunction.LatentAdjustPost
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {K U P : Type}

/-- The real initExtra tail after its source root operation. This internal
composition lemma covers both an existing root and one newly issued tag. -/
theorem initExtra_tagged [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (size : Size) (align : Align)
    (tracker : MachineHooks.BorrowState) (global : GlobalState) (root : BorTag)
    (tracked : machine.borrowTracker = some tracker)
    (tagged : tracker.global.rootPointerTag id = .ok (global,root))
    (noRace : machine.dataRace = none)
    (vacant : (extras.get machine.user).allocations.any (fun row => row.1 == id) = false) :
    GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align machine =
      .ok (BorrowTree.new root size)
        (MemoryExtras.putAllocation extras {machine with borrowTracker := some {tracker with global}} id {weakMemory := none}) := by
  have noentry : ¬ ∃ (i : Nat) (h : i < (extras.get machine.user).allocations.size),
      (extras.get machine.user).allocations[i].1=id := by
    simpa only [Array.any_eq_false,beq_iff_eq,not_exists] using vacant
  simp only [GlobalAllocationMachine.initExtra,tracked,tagged,
    bind,EStateM.bind,pure,EStateM.pure,Except.pure,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    noRace,Option.map_none,Option.getD_none]
  simp [MemoryExtras.initAllocation,vacant,MemoryExtras.putAllocation,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,
    set,MonadStateOf.set,EStateM.set,tryCatchThe,tryCatch,MonadExceptOf.tryCatch,EStateM.tryCatch,
    Bind.bind,noRace,noentry]

/-- Current raw root-tag headroom suffices for the actual initExtra operation,
including an uncached root. Arbitrary pre-existing live trees remain formed. -/
theorem initExtra [DecidableEq K]
    (extras : MemoryExtras.Hooks K U P) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (size : Size) (align : Align) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World machine tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 2^64)
    (noRace : machine.dataRace = none)
    (vacant : (extras.get machine.user).allocations.any (fun row => row.1 == id) = false) :
    ∃ global root,
      tracker.global.rootPointerTag id = .ok (global,root) ∧
      GlobalAllocationMachine.initExtra extras (fun _ _ _ => pure ()) id size align machine =
        .ok (BorrowTree.new root size)
          (MemoryExtras.putAllocation extras {machine with borrowTracker := some {tracker with global}} id {weakMemory := none}) ∧
      TreeRuntimeInput.World
        (MemoryExtras.putAllocation extras {machine with borrowTracker := some {tracker with global}} id {weakMemory := none})
        {tracker with global} ∧
      global.nextPointerTag.value.toNat ≤ tracker.global.nextPointerTag.value.toNat+1 := by
  obtain ⟨global,root,tagged,_protected,_tracked⟩ := RelocationRoot.root_tag_room tracker.global id tagRoom
  refine ⟨global,root,tagged,initExtra_tagged extras machine id size align tracker global root world.enabled tagged noRace vacant,?_,?_⟩
  · exact RootTagPost.world machine _ tracker global id root world rfl rfl tagged
  · exact (RootTagPost.root tracker.global id global root tagged).2.2.2.2.2.1

/-- The managed ownership-free adjust spine consumes an established actual
conversion result, then executes the actual root initialization and extras
registration. The machine proof derives conversion from its raw input theorem;
no successful operation is added to caller validity. -/
theorem adjust [DecidableEq K]
    (target : TargetDataLayout) (extras : MemoryExtras.Hooks K U P)
    (leaves : GlobalAllocationMachine.Leaves K U) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (before middle : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (prepare : leaves.bytes.prepare id (RelocationBytePrimitives.snapshot source) source.align =
      pure (RelocationBytePrimitives.snapshot source,none))
    (diagnostic : leaves.diagnostic = fun _ _ _ => pure ())
    (conversion : Allocation.adjustFromTcx source target
      (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
      leaves.globalRootPointer before = .ok converted middle)
    (attributes : RelocationByteFold.Attributes source converted)
    (world : TreeRuntimeInput.World middle tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 2^64)
    (noRace : middle.dataRace = none)
    (vacant : (extras.get middle.user).allocations.any (fun row => row.1 == id) = false) :
    ∃ global root,
      tracker.global.rootPointerTag id = .ok (global,root) ∧
      GlobalAllocationMachine.adjust target extras leaves id source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation extras {middle with borrowTracker := some {tracker with global}} id {weakMemory := none}) ∧
      TreeRuntimeInput.World
        (MemoryExtras.putAllocation extras {middle with borrowTracker := some {tracker with global}} id {weakMemory := none})
        {tracker with global} ∧
      global.nextPointerTag.value.toNat ≤ tracker.global.nextPointerTag.value.toNat+1 := by
  obtain ⟨global,root,tagged,initialized,postWorld,cost⟩ := initExtra extras middle id source.byteSize source.align tracker
    world tagRoom noRace vacant
  refine ⟨global,root,tagged,?_,postWorld,cost⟩
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
      .ok (RelocationBytePrimitives.snapshot source) := by
    cases source
    simp [RelocationBytePrimitives.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len,pure,Pure.pure,Except.pure,Except.toOption]
  simp only [GlobalAllocationMachine.adjust,inspect,prepare,conversion,attributes.size,attributes.align,
    GlobalAllocationMachine.init,diagnostic,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
  simp only [pure,Pure.pure] at initialized
  rw [initialized]
end EmptyFunction.LatentAdjustPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LatentAdjustPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent adjust post axiom {dependency} in {name}"
