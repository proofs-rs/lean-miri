import duplicate_prefix.GlobalDataOnlyExtra
import Miri.Input.EvalPointerSource

namespace DuplicatePrefix.GlobalDataOnlyActualBytes
open Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def leaves {Os R P H D O Aff B Host C : Type}
    (compiler : Miri.Input.CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (source : Miri.Input.EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (address : MachineAddress.Hooks MiriMemoryKind (Miri.Input.EvalPointerSource.Control Os R P H D O Aff B Host))
    (pointer : Pointer CtfeProvenance → Miri.Input.EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance)) :
    GlobalAllocationMachine.Leaves MiriMemoryKind (Miri.Input.EvalPointerSource.User Os R P H D O Aff B Host) where
  bytes := Miri.Input.EvalPointerSource.bytes compiler image source address
  globalRootPointer := pointer
  diagnostic := fun _ _ _ => pure ()

theorem adjust_exists {Os R P H D O Aff B Host C : Type}
    (compiler : Miri.Input.CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (extra : MemoryExtras.Hooks MiriMemoryKind (Miri.Input.EvalPointerSource.User Os R P H D O Aff B Host) P)
    (sourceLeaves : Miri.Input.EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (address : MachineAddress.Hooks MiriMemoryKind (Miri.Input.EvalPointerSource.Control Os R P H D O Aff B Host))
    (pointer : Pointer CtfeProvenance → Miri.Input.EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance))
    (before : Miri.Input.EvalPointerSource.Machine Os R P H D O Aff B Host)
    (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (managed : (sourceLeaves.nativeLibraryPaths before.user.payload.payload.user.host).isEmpty = true)
    (empty : source.provenanceMap = ProvenanceMap.new)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.dataRace = none)
    (noExtras : ((extra.get before.user).allocations.any (fun row => row.1 == id)) = false) :
    ∃ converted : Allocation Provenance Unit,
      GlobalDataOnlyConversion.Facts source converted ∧
      GlobalAllocationMachine.adjust compiler.runtime.target.base extra (leaves compiler image sourceLeaves address pointer) id source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation extra before id ⟨none,#[]⟩) := by
  obtain ⟨converted,conversion,facts⟩ := GlobalDataOnlyConversion.adjust_exists source compiler.runtime.target.base pointer before empty
  refine ⟨converted,facts,?_⟩
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
      .ok (AllocationCopy.snapshot source) := by
    cases source
    simp [AllocationCopy.snapshot, Allocation.inspectWithUninitAndPtrOutsideInterpreter,
      Allocation.len, pure, Pure.pure, Except.pure, Except.toOption]
  have init := GlobalDataOnlyExtra.init_extra extra before tracker id root source.byteSize source.align
    enabled rootCached race noExtras
  simp only [GlobalAllocationMachine.adjust, leaves, Miri.Input.EvalPointerSource.bytes, managed,
    inspect, conversion, facts.size, facts.align, GlobalAllocationMachine.init, init,
    get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, ite_true]
  simp only [pure, Pure.pure, EStateM.pure] at init
  rw [init]
end DuplicatePrefix.GlobalDataOnlyActualBytes

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GlobalDataOnlyActualBytes.adjust_exists) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved managed global conversion dependency {dependency}"
