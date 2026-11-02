import duplicate_prefix.ReferenceFactory
import duplicate_prefix.ProjectionMetadataFacts
import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.RootMetadataQueries
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ActualReferenceContext
noncomputable section
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open CanonicalConfigFacts
abbrev config (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) := PreparedContracts.actualConfig options () remaining span
abbrev adapted (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (pointers : RootPointers) :=
  TypedValidityProviders.retagHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime
    (config options remaining span).access (config options remaining span).validity.projection
    (config options remaining span).validity.vtable pointers () (config options remaining span).retag

structure Context (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) where
  pointers : RootPointers
  inner : ValidityMachine.Compiler MiriMemoryKind CanonicalConfigFacts.RootStored Unit
  innerDebug : inner.debugAssertions = (config options remaining span).compiler.debugAssertions
  innerAbi : inner.debugAbiCheck = (config options remaining span).compiler.debugAbiCheck
  visitor : RootEmptyReferenceValidity.VisitorFields (config options remaining span).validity
    (config options remaining span).access (config options remaining span).allocation inner
    (adapted options remaining span pointers) () options.limits.retag
  source : TypedRetagFields.SourceFields (adapted options remaining span pointers)
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts (config options remaining span).access
    (config options remaining span).validity.projection (config options remaining span).validity.vtable pointers ()
  pointer : (config options remaining span).validity.ptrToPlace =
    PointerPlaceMachine.fromImmediate (config options remaining span).access
      (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts)
  arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩
  resolve : (config options remaining span).access.resolvePointer = TypedMemoryProviders.resolvePointer pointers
  globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
    (PlaceMachine.AccessState MiriMemoryKind Machine.RootUser)
  globalKind : MiriMemoryKind
  ensure : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals
  synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}

theorem exists_context (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false) : Nonempty (Context options remaining span) := by
  let cfg := config options remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, table, discriminant, globals, validity, arithmetic, resolve, ensure, synchronize⟩ := fields.validitySources
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays cfg.projection pointers
  let base := ExecutionValidity.hooks queries cfg.access cfg.allocation cfg.compiler
    cfg.projection table discriminant cfg.retag options.limits.retag
  let hooks := TypedValidityProviders.visitor PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime cfg.access cfg.allocation cfg.compiler
    pointers cfg.retag options.limits.retag base
  have hooksEq : cfg.validity = hooks := by rw [validity]; rfl
  dsimp only [cfg] at hooksEq
  obtain ⟨inner, debug, noDebug, visitor, pointer, sources⟩ := ReferenceFactory.fields
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime base cfg.access cfg.allocation cfg.compiler
    pointers cfg.retag options.limits.retag () fields.retagLog
    (by rw [fields.retagPrecise, preciseOff]) (by rw [fields.retagImplicit, implicitOff])
  refine ⟨⟨pointers, inner, debug, noDebug, ?_, ?_, ?_, ?_, resolve, globals, .global, ensure, synchronize⟩⟩
  · simpa only [adapted, hooksEq] using visitor
  · simpa only [adapted, hooksEq] using sources
  · simpa only [hooksEq] using pointer
  · exact arithmetic

#print axioms exists_context

end
end DuplicatePrefix.ActualReferenceContext
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ActualReferenceContext.exists_context) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual reference context dependency {dependency}"
