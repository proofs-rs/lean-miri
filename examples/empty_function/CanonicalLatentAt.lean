import empty_function.CanonicalLatentEnsure
import empty_function.RelocationOrdinaryAt
namespace EmptyFunction.CanonicalLatentAt
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.CanonicalLatentMemory
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
/-- The raw caller packet remains anchored before frame/tag/protector setup.
Actual prefix projections and the derived reserved-tag fence transport only
what canonical lazy conversion reads. The source order is unchanged. -/
theorem ensure (s : WholeCall.Static) (p : WholeCall.Packet)
    (metadata : Specification.Metadata s) (input : InputDraft.CurrentInputDraft s p) (resources : Specification.ResourceMargins s p)
    (current : WholeCall.State)
    (memory : current.machine.memory = p.before.machine.memory)
    (addresses : current.machine.user.addresses = p.before.machine.user.addresses)
    (runtime : current.machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (tape : ChoiceExecution.tapeAccess.get current.machine = ChoiceExecution.tapeAccess.get p.before.machine)
    (thread : current.machine.threads.activeThread = p.before.machine.threads.activeThread)
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World current.machine tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+(resources.budget-1) < 2^64)
    (noRace : current.machine.dataRace = none) (reserved : BorTag) (fence : RootReservedPost.Fence tracker.global reserved)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (ordinary : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩) :
    ∃ (converted : Allocation Provenance Unit) (middle : ChoiceExecution.S)
      (afterTracker : MachineHooks.BorrowState) (global : GlobalState) (root : BorTag),
      RelocationByteFold.Attributes source converted ∧
      let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
      let adjusted := MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {afterTracker with global}} id {weakMemory := none}
      let installed := LatentInstallPost.installed adjusted id .global allocation
      s.cfg.retag.ensureTreeExtra id current = .ok () {current with machine := installed} ∧
      installed.memory.live.find? (fun row => row.1 == id) = some (id,⟨.machine .global,allocation⟩) ∧
      TreeRuntimeInput.World installed {afterTracker with global} ∧
      root ≠ reserved ∧ RootReservedPost.Fence global reserved ∧
      middle.memory = current.machine.memory ∧
      global.protectedTags = tracker.global.protectedTags ∧
      global.trackedPointerTags = tracker.global.trackedPointerTags ∧
      (∀ parentTag, tracker.global.rootTag? id = some parentTag → root = parentTag) ∧
      middle.threads = current.machine.threads ∧
      middle.user.payload.payload.user.runtime = current.machine.user.payload.payload.user.runtime ∧
      RelocationContext.view middle.user.payload = RelocationContext.view current.machine.user.payload ∧
      (∀ oldId tag, tracker.global.rootTag? oldId = some tag → global.rootTag? oldId = some tag) ∧
      Preservation.ExistingAddressFacts current {current with machine := installed} := by
  have pointerWidth : (CanonicalLatentMemory.source s).address.arithmetic = ⟨Size.ofBytes 8⟩ := by
    change (⟨s.prepared.compiler.runtime.target.pointerSize⟩ : PointerArithmetic) = _
    rw [metadata.pointerSize]
  obtain ⟨converted,middle,conversion,post,runtimeAnchor,attributes,_keys,_fragments⟩ := RelocationOrdinaryAt.convert
    s p input resources current.machine memory addresses runtime tape thread tracker world tagRoom noRace reserved fence
    id source selected absent noFunction noVaList descriptor ordinary s.prepared.compiler.runtime.target.base
    (CanonicalLatentMemory.source s).address
    ((reuse_actual ".Miri.Input.EvalPointerSource.externStatic") s.prepared.compiler s.prepared.image (CanonicalLatentMemory.source s).address)
    metadata.target pointerWidth
  obtain ⟨_memory,_threads,_runtime,context,addressFacts,middleRace,afterTracker,middleWorld,tags,middleFence,middleFrame⟩ := post
  have sourceInput := RelocationInput.memory_source s p input id source selected absent noFunction noVaList descriptor
  have spare := RelocationOrdinaryConversion.spare s p resources id source sourceInput.physical descriptor
  have tagOne : afterTracker.global.nextPointerTag.value.toNat+1 < 2^64 := by omega
  have vacancy := (reuse_actual ".EmptyFunction.CanonicalLatentMemory.vacant") s p input id source selected absent noFunction noVaList descriptor
  have middleVacant : ((extras s).get middle.user).allocations.any (fun row => row.1 == id) = false := by
    change middle.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false
    rw [runtimeAnchor]
    exact vacancy
  have actualConversion : Allocation.adjustFromTcx source s.prepared.compiler.runtime.target.base
      (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
      (globalLeaves s).globalRootPointer current.machine = .ok converted middle := conversion
  obtain ⟨global,root,tagged,adjusted,registeredWorld,_cost⟩ := LatentAdjustPost.adjust
    s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s) id source converted current.machine middle afterTracker
    (CanonicalDictionaries.global_bytes_prepare s.prepared.compiler s.prepared.image s.prepared s.options.place.debugAssertions
      id (RelocationBytePrimitives.snapshot source) source.align) rfl actualConversion attributes middleWorld tagOne middleRace middleVacant
  let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
  let after := MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {afterTracker with global}} id {weakMemory := none}
  have actual := LatentInstallPost.ensure s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
    (fun memory state definition =>
      let result := s.prepared.image.evaluateStaticInitializer {state with machine := {state.machine with memory}} definition
      ⟨result.state.machine.memory,result.state,result.outcome⟩)
    current after id .global source allocation (by simpa only [memory] using absent) (by simpa only [memory] using descriptor) adjusted
  have lookup := (RootTagPost.root afterTracker.global id global root tagged).1
  have formed := LatentTreePost.cached global registeredWorld.globals id root source.byteSize lookup
  have installedWorld := LatentInstallPost.world after {afterTracker with global} id .global allocation registeredWorld formed
  have rootFence := RootReservedPost.root afterTracker.global global id root reserved middleFence tagged
  have capacityPositive : 1 ≤ s.capacity := by
    have reserve := resources.reserve
    have capacity := resources.capacity
    unfold Specification.work at reserve
    omega
  have fields := CanonicalDictionaries.global_fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (leaves s) (s.capacity-1) metadata.construction s.cfg
      (by rw [Nat.sub_add_cancel capacityPositive]; exact s.built)
  have framePost := RootFramePost.trans tracker.global afterTracker.global global (middleFrame tracker world.enabled)
    (RootFramePost.root afterTracker.global global id root tagged)
  refine ⟨converted,middle,afterTracker,global,root,attributes,?_,LatentInstallPost.live_row after id .global allocation,
    installedWorld,rootFence.2,rootFence.1,_memory,framePost.1,framePost.2.1,?_,_threads,_runtime,context,framePost.2.2,addressFacts⟩
  · rw [fields.ensure,fields.globalConstruction]
    exact actual
  · intro parentTag prior
    exact Option.some.inj (lookup.symm.trans (framePost.2.2 id parentTag prior))
end EmptyFunction.CanonicalLatentAt
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalLatentAt.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical latent prefix axiom {dependency} in {name}"
