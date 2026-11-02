import duplicate_prefix.SliceLenFacts
namespace DuplicatePrefix.SliceLenRawRetag
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def rawShape : Miri.TreeBorrows.RetagPipeline.RetagTypeShape :=
  {isReference := false,isRawPointer := true}

theorem raw_retag_none [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value : RvalueImmTy Provenance) (ty : TyId)
    (shape : h.typeShape ty = pure rawShape) :
    TypedRetag.retagPtrValue h budget value ty .Raw = pure none := by
  unfold TypedRetag.retagPtrValue
  rw [shape]
  rfl

theorem raw_scope_unchanged [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value : RvalueImmTy Provenance) (ty : TyId)
    (shape : h.typeShape ty = pure rawShape) :
    MachineHooks.withRetagMode .Raw (do
      let result ← TypedRetag.machineRetagPtrValue h budget value ty
      pure (result.getD value)) = pure value := by
  funext state
  have raw := raw_retag_none h budget value ty shape
  unfold MachineHooks.withRetagMode
  cases tracked : state.machine.borrowTracker with
  | none =>
    simp [tracked,TypedRetag.machineRetagPtrValue,get,getThe,MonadStateOf.get,EStateM.get,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  | some tracker =>
    simp [tracked,TypedRetag.machineRetagPtrValue,raw,get,getThe,MonadStateOf.get,EStateM.get,
      set,MonadStateOf.set,EStateM.set,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    rw [← tracked]

theorem actual_raw_shape (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).retag.typeShape 154 = pure rawShape := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).retagTypeShape]
  funext state
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = RootMetadataQueries.context from rfl]
  dsimp only
  rw [SliceLenFacts.raw_type_shape]
  rfl

#print axioms raw_scope_unchanged
#print axioms actual_raw_shape
end
end DuplicatePrefix.SliceLenRawRetag
