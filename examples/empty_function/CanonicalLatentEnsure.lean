import empty_function.CanonicalLatentMemory
import empty_function.LatentInstallPost
import empty_function.LatentTreePost
namespace EmptyFunction.CanonicalLatentEnsure
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.CanonicalLatentMemory
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
theorem ensure (s : WholeCall.Static) (p : WholeCall.Packet)
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
      let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
      let adjusted := MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {tracker with global}} id {weakMemory := none}
      let installed := LatentInstallPost.installed adjusted id .global allocation
      s.cfg.retag.ensureTreeExtra id p.before = .ok () {p.before with machine := installed} ∧
      installed.memory.live.find? (fun row => row.1 == id) = some (id,⟨.machine .global,allocation⟩) ∧
      TreeRuntimeInput.World installed {tracker with global} ∧
      tracker.global.rootPointerTag id = .ok (global,root) := by
  obtain ⟨converted,middle,tracker,global,root,attributes,tagged,adjusted,world,_memory,_cost⟩ :=
    CanonicalLatentMemory.convert s p metadata input resources profile id source selected absent noFunction noVaList descriptor ordinary
  have capacityPositive : 1 ≤ s.capacity := by
    have reserve := resources.reserve
    have capacity := resources.capacity
    unfold Specification.work at reserve
    omega
  have fields := CanonicalDictionaries.global_fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (leaves s) (s.capacity-1) metadata.construction s.cfg
      (by rw [Nat.sub_add_cancel capacityPositive]; exact s.built)
  let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
  let after := MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {tracker with global}} id {weakMemory := none}
  have actual := LatentInstallPost.ensure s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
    (fun memory state definition =>
      let result := s.prepared.image.evaluateStaticInitializer {state with machine := {state.machine with memory}} definition
      ⟨result.state.machine.memory,result.state,result.outcome⟩)
    p.before after id .global source allocation absent descriptor adjusted
  have lookup := (RootTagPost.root tracker.global id global root tagged).1
  have formed := LatentTreePost.cached global world.globals id root source.byteSize lookup
  have installedWorld := LatentInstallPost.world after {tracker with global} id .global allocation world formed
  refine ⟨converted,middle,tracker,global,root,attributes,?_,LatentInstallPost.live_row after id .global allocation,installedWorld,tagged⟩
  rw [fields.ensure,fields.globalConstruction]
  exact actual
end EmptyFunction.CanonicalLatentEnsure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalLatentEnsure.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical latent ensure axiom {dependency} in {name}"
