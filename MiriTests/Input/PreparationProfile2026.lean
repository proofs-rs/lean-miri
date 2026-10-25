import Miri.Input.EvalPreparation

/-! Profiling options may add observation events but must not alter any
preparation result, including failed outcomes and partial imported memory. -/
namespace Miri.Input.PreparationProfile2026

theorem lifecycleProfiledIdentity (profile : Lean.Options)
    (calls : CompilerCallPipeline.Prepared) :
    CompilerLifecyclePipeline.prepareProfiled profile calls =
      CompilerLifecyclePipeline.prepare calls := by
  rfl

theorem constantsProfiledIdentity (profile : Lean.Options)
    (program : LoweredProgram) :
    CompilerConstantQueries.prepareProfiled profile program =
      CompilerConstantQueries.prepare program := by
  rfl

theorem callPipelineProfiledIdentity (profile : Lean.Options)
    (program : LoweredProgram) :
    CompilerCallPipeline.prepareProfiled profile program =
      CompilerCallPipeline.prepare program := by
  rfl

theorem providersProfiledIdentity (profile : Lean.Options)
    (program : LoweredProgram) :
    CompilerProviders.prepareProfiled profile program =
      CompilerProviders.prepare program := by
  rfl

theorem evalPreparationProfiledIdentity (profile : Lean.Options)
    (program : LoweredProgram) :
    EvalPreparation.prepareProfiled profile program =
      EvalPreparation.prepare program := by
  rfl

end Miri.Input.PreparationProfile2026

#print axioms Miri.Input.PreparationProfile2026.callPipelineProfiledIdentity
#print axioms Miri.Input.PreparationProfile2026.lifecycleProfiledIdentity
#print axioms Miri.Input.PreparationProfile2026.constantsProfiledIdentity
#print axioms Miri.Input.PreparationProfile2026.providersProfiledIdentity
#print axioms Miri.Input.PreparationProfile2026.evalPreparationProfiledIdentity
