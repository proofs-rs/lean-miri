import duplicate_prefix.AsMutPtrFacts
import duplicate_prefix.CanonicalConfigFacts

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.AsMutPtrRawRetag
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows

theorem raw_pointer_no_permission [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (value : RvalueImmTy Provenance) (ty : TyId)
    (shape : hooks.typeShape ty = pure ⟨false, false, true, false⟩) :
    TypedRetag.retagPtrValue hooks budget value ty .Raw = pure none := by
  funext state
  unfold TypedRetag.retagPtrValue
  simp [shape, RetagPipeline.RetagTypeShape.classify, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]

theorem raw_scope_identity [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (value : RvalueImmTy Provenance) (ty : TyId)
    (shape : hooks.typeShape ty = pure ⟨false, false, true, false⟩)
    (state : MachineHooks.State K U) :
    MachineHooks.withRetagMode .Raw (do
      let changed ← TypedRetag.machineRetagPtrValue hooks budget value ty
      pure (changed.getD value)) state = .ok value state := by
  have raw := raw_pointer_no_permission hooks budget value ty shape
  cases tracked : state.machine.borrowTracker with
  | none =>
    simp [MachineHooks.withRetagMode, TypedRetag.machineRetagPtrValue, tracked,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
  | some tracker =>
    simp [MachineHooks.withRetagMode, TypedRetag.machineRetagPtrValue, tracked, raw,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    change {state with machine := {state.machine with borrowTracker := some tracker}} = state
    rw [← tracked]

theorem actual_raw_scope_identity
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (value : RvalueImmTy Provenance) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).withRetagMode () .Raw
      (do
        let changed ← (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).retagPtrValue () value 204
        pure (changed.getD value)) state = .ok value state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have shape : config.retag.typeShape 204 = pure ⟨false, false, true, false⟩ := by
    rw [fields.retagTypeShape]
    funext observed
    change (match CompilerFacts.retagTypeShape RootMetadataQueries.context 204 with
      | .ok kind => EStateM.Result.ok kind observed
      | .error reason => EStateM.Result.error (StepError.unsupported reason) observed) =
      .ok ⟨false, false, true, false⟩ observed
    rw [AsMutPtrFacts.raw_retag_shape]
  change MachineHooks.withRetagMode .Raw (do
    let changed ← TypedRetag.machineRetagPtrValue config.retag limits.retag value 204
    pure (changed.getD value)) state = _
  exact raw_scope_identity config.retag limits.retag value 204 shape state

open Lean Elab Command in
run_cmd do
  for declaration in [``raw_pointer_no_permission, ``raw_scope_identity, ``actual_raw_scope_identity] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.AsMutPtrRawRetag
