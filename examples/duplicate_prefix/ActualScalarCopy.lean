import duplicate_prefix.ScalarCopyStage
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.CopyCompilerFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.ActualScalarCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem actual_copy_scalar
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (scalar : Miri.ABI.Scalar) (repr : layout.layout.backendRepr = .Scalar scalar)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).copyOp
      () ⟨.immediate value, layout⟩ dest =
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () value dest := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have compatible : (ExecutionMachine.withValidation config limits).copy.compatible =
      CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have padding : (ExecutionMachine.withValidation config limits).copy.hasPadding =
      CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false := by
    change config.copy.hasPadding = _
    rw [fields.copyPadding, debugOff]
  exact ScalarCopyStage.rvalue_copy_immediate config limits PreparedReflection.actual.compiler ()
    layout value dest destLayout scalar repr sized compatible padding
    (CanonicalConfigFacts.actual_retain_touched options () remaining span)

theorem actual_copy_no_padding
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (noPadding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false layout = .ok false)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).copyOp
      () ⟨.immediate value, layout⟩ dest =
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () value dest := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have compatible : (ExecutionMachine.withValidation config limits).copy.compatible =
      CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have padding : (ExecutionMachine.withValidation config limits).copy.hasPadding =
      CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false := by
    change config.copy.hasPadding = _
    rw [fields.copyPadding, debugOff]
  exact ScalarCopyStage.rvalue_copy_no_padding config limits PreparedReflection.actual.compiler ()
    layout value dest destLayout noPadding sized compatible padding
    (CanonicalConfigFacts.actual_retain_touched options () remaining span)

theorem usize_sized : RootCompilerFacts.usizeLayout.layout.isSized = true := by decide +kernel

theorem actual_copy_usize
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (n : UInt64) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = RootCompilerFacts.usizeLayout) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).copyOp
      () ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩ dest =
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))) dest := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.usizeLayout
    CopyCompilerFacts.primitive_layouts_initialized.2.2.2
  exact actual_copy_scalar options limits remaining span debugOff RootCompilerFacts.usizeLayout _ dest
    destLayout _ repr usize_sized

#print axioms actual_copy_usize
open Lean Elab Command in
run_cmd do
  for declaration in [``actual_copy_no_padding, ``actual_copy_scalar, ``usize_sized, ``actual_copy_usize] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.ActualScalarCopy
