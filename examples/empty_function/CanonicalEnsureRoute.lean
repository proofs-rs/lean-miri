import empty_function.SelectedMaterializationFacts
import empty_function.MaterializationPreservation
import empty_function.StaticOwnedPost
import empty_function.InitializationPrefix
namespace EmptyFunction.CanonicalEnsureRoute
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.MaterializationPreservation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev initializer (s : Static) :=
  fun (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (state : PlaceMachine.AccessState MiriMemoryKind Configuration.RootUser) (definition : Nat) =>
    let result := s.prepared.image.evaluateStaticInitializer {state with machine := {state.machine with memory}} definition
    (⟨result.state.machine.memory,result.state,result.outcome⟩ : GlobalMemoryHookResult Provenance BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind Configuration.RootUser) (Allocation CtfeProvenance Unit))

theorem fields (s : Static) (metadata : Specification.Metadata s) :
    CanonicalDictionaries.GlobalFields s.prepared.compiler s.prepared.image (leaves s) s.cfg := by
  apply CanonicalDictionaries.global_fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (leaves s) (s.capacity-1) metadata.construction s.cfg
  rw [Nat.sub_add_cancel (show 1 ≤ s.capacity from InitializationPrefix.capacity_positive s)]
  exact s.built

/-- Canonical configuration identity and raw selected-source data preserve
an actual adjustment error across both memory and static getter branches. -/
theorem error (s : Static) (metadata : Specification.Metadata s) (p : Packet)
    (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id source)
    (current : State) (memory : current.machine.memory = p.before.machine.memory)
    (reason : StepError) (failed : ChoiceExecution.S)
    (adjusted : GlobalAllocationMachine.adjust s.prepared.compiler.runtime.target.base
      (extras s) (globalLeaves s) id source current.machine = .error reason failed) :
    s.cfg.retag.ensureTreeExtra id current = .error reason {current with machine := failed} := by
  rw [(fields s metadata).ensure,(fields s metadata).globalConstruction]
  change GlobalAllocationMachine.ensure .global
    (GlobalAllocationMachine.hooks s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s) (initializer s)) id current = _
  cases selected with
  | memory _ absent _ _ descriptor =>
    exact GlobalErrorAware.ensure_adjust_error s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
      (initializer s) current failed id .global source reason (by simpa only [memory] using absent)
      (by simpa only [memory] using descriptor) adjusted
  | internalStatic definition _ absent _ _ descriptor evaluated =>
    apply GlobalErrorAware.ensure_static_adjust_error s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
      (initializer s) current failed id .global definition source reason (by simpa only [memory] using absent)
      (by simpa only [memory] using descriptor) ?_ adjusted
    simp [initializer,AllocationImage.Imported.evaluateStaticInitializer,evaluated]

/-- Source-owned successful adjustment follows the same canonical getter and
inserts the actual new tree without changing the caller stack. -/
theorem owned (s : Static) (metadata : Specification.Metadata s) (p : Packet)
    (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id source)
    (current : State) (memory : current.machine.memory = p.before.machine.memory)
    (allocation : Allocation Provenance BorrowTree) (middle : ChoiceExecution.S)
    (adjusted : GlobalAllocationMachine.adjust s.prepared.compiler.runtime.target.base
      (extras s) (globalLeaves s) id source current.machine = .ok (.owned allocation) middle) :
    s.cfg.retag.ensureTreeExtra id current =
      .ok () {current with machine := GlobalErrorAware.installed middle id .global allocation} := by
  rw [(fields s metadata).ensure,(fields s metadata).globalConstruction]
  change GlobalAllocationMachine.ensure .global
    (GlobalAllocationMachine.hooks s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s) (initializer s)) id current = _
  cases selected with
  | memory _ absent _ _ descriptor =>
    exact GlobalErrorAware.ensure_owned s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
      (initializer s) current middle id .global source allocation (by simpa only [memory] using absent)
      (by simpa only [memory] using descriptor) adjusted
  | internalStatic definition _ absent _ _ descriptor evaluated =>
    apply StaticOwnedPost.ensure_owned s.prepared.compiler.runtime.target.base (extras s) (globalLeaves s)
      (initializer s) current middle id .global definition source allocation (by simpa only [memory] using absent)
      (by simpa only [memory] using descriptor) ?_ adjusted
    simp [initializer,AllocationImage.Imported.evaluateStaticInitializer,evaluated]
end EmptyFunction.CanonicalEnsureRoute

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalEnsureRoute.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common-ensure axiom {dependency} in {name}"
