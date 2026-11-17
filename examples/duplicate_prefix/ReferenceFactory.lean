import duplicate_prefix.RootEmptyReferenceValidity

/-! Close the real reference visitor dictionaries against their source factory. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ReferenceFactory
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter

theorem fields {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (choice : C)
    (log : retag.logCreation = fun _ _ _ _ _ => pure ())
    (precise : retag.preciseInteriorMut = pure false)
    (implicitWrites : retag.implicitWrites = pure false) :
    let hooks := TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag budget base
    let adapted := TypedValidityProviders.retagHooks prepared runtime access hooks.projection hooks.vtable pointers choice retag
    ∃ inner : ValidityMachine.Compiler K U C,
      inner.debugAssertions = compiler.debugAssertions ∧
      inner.debugAbiCheck = compiler.debugAbiCheck ∧
      RootEmptyReferenceValidity.VisitorFields hooks access allocation inner adapted choice budget ∧
      hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) ∧
      TypedRetagFields.SourceFields adapted prepared access hooks.projection hooks.vtable pointers choice := by
  dsimp only
  obtain ⟨inner, debug, noDebug, toOp, read, write, pointer, check, align, nonnull, ghost, retagAction⟩ :=
    ReferenceVisitorFields.typed_reference_fields prepared runtime base access allocation compiler pointers retag budget
  refine ⟨ValidityMachine.compilerPolicy inner, debug, noDebug, ?_, pointer, ?_⟩
  · refine ⟨toOp, ghost, read, write, check, align, nonnull, congrFun retagAction choice, ?_⟩
    rfl
  · exact TypedRetagFields.adapted_sources prepared runtime access _ _ pointers choice retag log precise implicitWrites

#print axioms fields
end DuplicatePrefix.ReferenceFactory
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ReferenceFactory.fields) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved reference factory dependency {dependency}"
