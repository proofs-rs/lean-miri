import empty_function.RelocationOrdinaryConversion
import empty_function.LatentAdjustPost
import empty_function.CanonicalDictionaries
namespace EmptyFunction.CanonicalLatentMemory
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
abbrev leaves (s : WholeCall.Static) := Configuration.leaves s.prepared s.options.place.debugAssertions
abbrev source (s : WholeCall.Static) := CanonicalDictionaries.pointerSource s.prepared.compiler s.prepared.image (leaves s)
abbrev globalLeaves (s : WholeCall.Static) := CanonicalDictionaries.globalLeaves s.prepared.compiler s.prepared.image (leaves s)
abbrev extras (s : WholeCall.Static) := EvalCoreMachine.extras (leaves s).sync ConcurrencyErrors.storeBuffer

private theorem vacant (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (id : AllocId) (allocation : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,allocation.byteSize,allocation.align,allocation.mutability,some (.memory allocation)⟩) :
    ((extras s).get p.before.machine.user).allocations.any (fun row => row.1 == id) = false := by
  have backing := RelocationInput.selected_backing s p input id selected
  cases backing with
  | live entry row => rw [absent] at row; cases row
  | global entry query _ _ _ registry =>
    have same := Option.some.inj (query.symm.trans descriptor)
    cases same
    exact registry absent (Or.inl rfl)
  | extraFunction row =>
    unfold MemoryState.hasExtraFunctionId at row
    have impossible : p.before.machine.memory.hasFunctionPointer id = true := by
      simp only [MemoryState.hasFunctionPointer,row,Bool.true_or]
    rw [noFunction] at impossible
    cases impossible
  | vaList row => rw [noVaList] at row; cases row
  | dead _ _ _ _ _ noGlobal => rw [descriptor] at noGlobal; cases noGlobal

/-- The ordinary-memory branch uses the actual canonical root callback, byte
backend and extras registry. Compiler metadata determines the pointer width. -/
theorem convert (s : WholeCall.Static) (p : WholeCall.Packet)
    (metadata : Specification.Metadata s) (input : InputDraft.CurrentInputDraft s p) (resources : Specification.ResourceMargins s p)
    (profile : Specification.RuntimeProfile s p) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (ordinary : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩) :
    ∃ (converted : Allocation Provenance Unit) (middle : ChoiceExecution.S)
      (tracker : MachineHooks.BorrowState) (global : GlobalState) (root : BorTag),
      RelocationByteFold.Attributes source converted ∧
      tracker.global.rootPointerTag id = .ok (global,root) ∧
      GlobalAllocationMachine.adjust s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s) id source p.before.machine =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {tracker with global}} id {weakMemory := none}) ∧
      TreeRuntimeInput.World
        (MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {tracker with global}} id {weakMemory := none})
        {tracker with global} ∧ middle.memory = p.before.machine.memory ∧
      global.nextPointerTag.value.toNat ≤ tracker.global.nextPointerTag.value.toNat+1 := by
  have pointerWidth : (CanonicalLatentMemory.source s).address.arithmetic = ⟨Size.ofBytes 8⟩ := by
    change (⟨s.prepared.compiler.runtime.target.pointerSize⟩ : PointerArithmetic) = _
    rw [metadata.pointerSize]
  obtain ⟨converted,middle,conversion,post,attributes,_keys,_fragments⟩ := RelocationOrdinaryConversion.convert s p input resources
    profile id source selected absent noFunction noVaList descriptor ordinary s.prepared.compiler.runtime.target.base
    (CanonicalLatentMemory.source s).address
    ((reuse_actual ".Miri.Input.EvalPointerSource.externStatic") s.prepared.compiler s.prepared.image (CanonicalLatentMemory.source s).address)
    metadata.target pointerWidth
  obtain ⟨memory,_threads,runtime,_context,noRace,tracker,world,tags⟩ := post
  have sourceInput := RelocationInput.memory_source s p input id source selected absent noFunction noVaList descriptor
  have spare := RelocationOrdinaryConversion.spare s p resources id source sourceInput.physical descriptor
  have tagOne : tracker.global.nextPointerTag.value.toNat+1 < 2^64 := by omega
  have vacancy := vacant s p input id source selected absent noFunction noVaList descriptor
  have middleVacant : ((extras s).get middle.user).allocations.any (fun row => row.1 == id) = false := by
    change middle.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false
    rw [runtime]
    exact vacancy
  have actualConversion : Allocation.adjustFromTcx source s.prepared.compiler.runtime.target.base
      (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
      (globalLeaves s).globalRootPointer p.before.machine = .ok converted middle := conversion
  obtain ⟨global,root,tagged,adjusted,worldPost,cost⟩ := LatentAdjustPost.adjust
    s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s) id source converted p.before.machine middle tracker
    (CanonicalDictionaries.global_bytes_prepare s.prepared.compiler s.prepared.image s.prepared s.options.place.debugAssertions
      id (RelocationBytePrimitives.snapshot source) source.align) rfl actualConversion attributes world tagOne noRace middleVacant
  exact ⟨converted,middle,tracker,global,root,attributes,tagged,adjusted,worldPost,memory,cost⟩
end EmptyFunction.CanonicalLatentMemory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalLatentMemory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical latent memory axiom {dependency} in {name}"
