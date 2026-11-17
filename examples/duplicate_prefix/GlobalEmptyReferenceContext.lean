import duplicate_prefix.GlobalDataOnlyActualConfig
import duplicate_prefix.ActualReferenceContext

namespace DuplicatePrefix.GlobalEmptyReferenceContext
open Miri Miri.Input Miri.ABI Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem make_sources (p : CompilerProviders.Prepared)
    (image : AllocationImage.Imported) (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options) (leaves : Machine.RootLeaves)
    (choice : Unit) (remaining : Nat) (contract : PreparedContracts.CompilerConstruction p) :
    ∃ config, EvalConfigurationCore.make p image bytes options leaves choice (remaining + 1) = .ok config ∧
      ∃ (sourcePointers : RootPointers) (vtable : RootVTable) (discriminant : RootDiscriminant)
        (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
          (PlaceMachine.AccessState MiriMemoryKind Machine.RootUser)),
        config.validity = EvalValidityMachine.hooks p.lifecycle.calls.symbols.facts p.lifecycle.calls.runtime
          (CompilerValidityLeaves.make p image EvalProjectionMachine.arrays config.projection sourcePointers)
          config.access config.allocation config.compiler config.projection vtable discriminant
          sourcePointers config.retag options.limits.retag ∧
        sourcePointers.arithmetic = ⟨p.runtime.target.pointerSize⟩ ∧
        config.access.resolvePointer = TypedMemoryProviders.resolvePointer sourcePointers ∧
        sourcePointers.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals ∧
        globals.synchronizeMemory = (fun memory view => {view with machine := {view.machine with memory}}) ∧
        sourcePointers = GlobalDataOnlyActualConfig.pointers p image leaves choice := by
  unfold EvalConfigurationCore.make
  unfold_factory_helpers
  rw [EvalConfigurationCore.makeWithForeignContext]
  simp (config := {zeta := false}) only [contract.maximum_eq]
  unfold_factory_helpers
  simp (config := {zeta := false}) only [EvalMathMachine.hooks,
    CompilerCallConstruction.helpers, contract.i32_eq, contract.bool_eq,
    contract.u8_eq, contract.unit_eq, contract.rootSpan_eq,
    Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  supply_validity_sources
  · with_unfolding_all rfl
  · simp only [Option.map_none, Option.map_some, EvalAccessMachine.make,
        EvalBackendMachine.access] <;> rfl
  · with_unfolding_all rfl
  · constructor <;> with_unfolding_all rfl

theorem actual_sources (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    let cfg := PreparedContracts.actualConfig options choice remaining span
    ∃ (sourcePointers : RootPointers) (vtable : RootVTable) (discriminant : RootDiscriminant)
      (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (PlaceMachine.AccessState MiriMemoryKind Machine.RootUser)),
      cfg.validity = EvalValidityMachine.hooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
        PreparedReflection.actual.compiler.lifecycle.calls.runtime
        (CompilerValidityLeaves.make PreparedReflection.actual.compiler PreparedReflection.actual.image
          EvalProjectionMachine.arrays cfg.projection sourcePointers)
        cfg.access cfg.allocation cfg.compiler cfg.projection vtable discriminant
        sourcePointers cfg.retag options.limits.retag ∧
      sourcePointers.arithmetic = ⟨PreparedReflection.actual.compiler.runtime.target.pointerSize⟩ ∧
      cfg.access.resolvePointer = TypedMemoryProviders.resolvePointer sourcePointers ∧
      sourcePointers.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals ∧
      globals.synchronizeMemory = (fun memory view => {view with machine := {view.machine with memory}}) ∧
      sourcePointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler PreparedReflection.actual.image
        (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) choice := by
  obtain ⟨config,construction,field⟩ := make_sources PreparedReflection.actual.compiler
    PreparedReflection.actual.image PreparedReflection.actual.bytes options
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
    choice remaining (PreparedContracts.actualConstruction span)
  have eq := PreparedContracts.actualConfig_eq options choice remaining span
  change EvalConfigurationCore.make PreparedReflection.actual.compiler PreparedReflection.actual.image
    PreparedReflection.actual.bytes options
    (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions)
    choice (remaining + 1) = .ok _ at eq
  rw [construction] at eq
  have same : config = PreparedContracts.actualConfig options choice remaining span := Except.ok.inj eq
  exact same ▸ field
open ActualReferenceContext
noncomputable section

theorem exists_context (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false) : ∃ ctx : ActualReferenceContext.Context options remaining span,
      ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler PreparedReflection.actual.image
        (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) () := by
  let cfg := config options remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, table, discriminant, globals, validity, arithmetic, resolve, ensure, synchronize,pointerEq⟩ := actual_sources options () remaining span
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
  refine ⟨⟨pointers, inner, debug, noDebug, ?_, ?_, ?_, ?_, resolve, globals, .global, ensure, synchronize⟩,pointerEq⟩
  · simpa only [adapted, hooksEq] using visitor
  · simpa only [adapted, hooksEq] using sources
  · simpa only [hooksEq] using pointer
  · exact arithmetic

end
end DuplicatePrefix.GlobalEmptyReferenceContext

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GlobalEmptyReferenceContext.actual_sources,
      ``DuplicatePrefix.GlobalEmptyReferenceContext.exists_context] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved actual global reference context dependency {dependency}"
