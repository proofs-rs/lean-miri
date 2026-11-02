import duplicate_prefix.GlobalDataOnlyExtra

namespace DuplicatePrefix.GlobalDataOnlyAdjust
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def leaves {K U : Type}
    (pointer : Pointer CtfeProvenance → GlobalAllocationMachine.M K U (Pointer Provenance)) :
    GlobalAllocationMachine.Leaves K U where
  bytes := GlobalAllocationMachine.managedBytes
  globalRootPointer := pointer
  diagnostic := fun _ _ _ => pure ()

theorem adjust_exists {K U P : Type} [DecidableEq K]
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
      GlobalDataOnlyConversion.Facts source converted ∧
      GlobalAllocationMachine.adjust target extras (leaves pointer) id source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation extras before id ⟨none,#[]⟩) := by
  obtain ⟨converted,conversion,facts⟩ := GlobalDataOnlyConversion.adjust_exists source target pointer before empty
  refine ⟨converted,facts,?_⟩
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
      .ok (AllocationCopy.snapshot source) := by
    cases source
    simp [AllocationCopy.snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len, pure, Pure.pure, Except.pure, Except.toOption]
  have init := GlobalDataOnlyExtra.init_extra extras before tracker id root source.byteSize source.align
    enabled rootCached race noExtras
  simp only [GlobalAllocationMachine.adjust, leaves, GlobalAllocationMachine.managedBytes,
    inspect, conversion, facts.size, facts.align, GlobalAllocationMachine.init, init,
    get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]
  simp only [pure, Pure.pure, EStateM.pure] at init
  rw [init]
end DuplicatePrefix.GlobalDataOnlyAdjust

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GlobalDataOnlyAdjust.adjust_exists) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved managed global conversion dependency {dependency}"
