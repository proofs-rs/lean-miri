import duplicate_prefix.GlobalSupportedImage
import duplicate_prefix.GlobalDataOnlyMaterialize

/-! Lazy non-TLS, non-extern STATIC sources through the actual exported
initializer query. Initializer availability is explicit INITIAL IMAGE DATA,
not a successful runtime operation assumption. Real CTFE relocation conversion,
byte attributes, BorrowTree root and allocation cache insertion are derived. -/
namespace DuplicatePrefix.StaticGlobalActualSource
open Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open GlobalDataOnlyMaterialize
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem get_raw {Os R P H D O Aff B Host C : Type}
    (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalPointerSource.User Os R P H D O Aff B Host) P)
    (sourceLeaves : EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (choice : C)
    (before : EvalPointerSource.Machine Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (initializer : image.initializers.find? (·.1 == definition) = some (definition,source))
    (managed : (sourceLeaves.nativeLibraryPaths before.user.payload.payload.user.host).isEmpty = true)
    (supported : GlobalSupportedImage.Supported source compiler.runtime.target before.memory
      tracker.global.rootPointerTags before.user.addresses.baseAddr)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == id)) = false)
    (absent : (before.memory.live.find? (fun old => old.1 == id)) = none)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
      MemoryLifecycle.getAllocRaw before.memory ⟨before,none⟩ id (some .global)
        (EvalPointerSource.make compiler image extras sourceLeaves choice).globals =
          ⟨(cached extras before id .global allocation).memory,
            ⟨cached extras before id .global allocation,none⟩,.ok allocation⟩ := by
  obtain ⟨converted,facts,adjust⟩ := GlobalSupportedImage.adjust_exists compiler image extras sourceLeaves choice before tracker
    id root source managed supported enabled rootCached race noExtras
  refine ⟨converted,facts,?_⟩
  simp only [MemoryLifecycle.getAllocRaw,absent,MemoryLifecycle.getGlobalAlloc,descriptor,
    EvalPointerSource.make, EvalGlobalAllocationMachine.make, GlobalAllocationMachine.hooks, AllocationImage.Imported.evaluateStaticInitializer,initializer,Id.run, bind, Bind.bind, pure, Pure.pure]
  unfold_global_data ".Miri.Interpreter.GlobalAllocationMachine.bridge"
  simp only [GlobalDataOnlyActualBytes.leaves, EvalPointerSource.make, pure, Pure.pure, EStateM.pure] at adjust
  simp only [adjust, Id.run, bind, Bind.bind, pure, Pure.pure]
  unfold_global_data ".Miri.Memory.MemoryState.insertLive"
  rfl
theorem ensure {Os R P H D O Aff B Host C : Type}
    (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalPointerSource.User Os R P H D O Aff B Host) P)
    (sourceLeaves : EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (choice : C)
    (before : MachineHooks.State MiriMemoryKind (EvalPointerSource.User Os R P H D O Aff B Host)) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (initializer : image.initializers.find? (·.1 == definition) = some (definition,source))
    (managed : (sourceLeaves.nativeLibraryPaths before.machine.user.payload.payload.user.host).isEmpty = true)
    (supported : GlobalSupportedImage.Supported source compiler.runtime.target before.machine.memory
      tracker.global.rootPointerTags before.machine.user.addresses.baseAddr)
    (enabled : before.machine.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root)
    (race : before.machine.dataRace = none)
    (noExtras : ((extras.get before.machine.user).allocations.any (fun row => row.1 == id)) = false)
    (absent : (before.machine.memory.live.find? (fun old => old.1 == id)) = none)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      (EvalPointerSource.make compiler image extras sourceLeaves choice).pointers.ensureTreeExtra id before =
        .ok () {before with machine := (cached extras before.machine id .global
          (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))} := by
  obtain ⟨converted,facts,raw⟩ := get_raw compiler image extras sourceLeaves choice before.machine tracker id root definition source initializer
    managed supported enabled rootCached race noExtras absent descriptor
  refine ⟨converted,facts,?_⟩
  simp only [EvalPointerSource.make, pure, Pure.pure, EStateM.pure] at raw
  simp only [EvalPointerSource.make, PointerSource.pointers, GlobalAllocationMachine.ensure, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, Pure.pure, EStateM.pure, raw]

end DuplicatePrefix.StaticGlobalActualSource

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.StaticGlobalActualSource.get_raw,
      ``DuplicatePrefix.StaticGlobalActualSource.ensure] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved static materialization dependency {dependency}"
