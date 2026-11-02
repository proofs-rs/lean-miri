import duplicate_prefix.ReferenceBorrowDriver
import duplicate_prefix.ActualReferenceMetadata

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.ActualRetagContext
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext RootMetadataQueries
noncomputable section

structure Context (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) where
  pointers : RootPointers
  table : RootRawVTable
  choice : Unit
  source : TypedRetagFields.SourceFields (config options remaining span).retag
    ReferenceMetadataFacts.prepared (config options remaining span).access
    (config options remaining span).projection table pointers choice
  arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩
  resolve : (config options remaining span).access.resolvePointer = TypedMemoryProviders.resolvePointer pointers
  globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
    (PlaceMachine.AccessState MiriMemoryKind Machine.RootUser)
  ensure : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals
  synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}
  construction : (config options remaining span).retag = EvalRetagMachine.hooks
    ReferenceMetadataFacts.prepared PreparedReflection.actual.compiler.lifecycle.calls.runtime
    (CompilerRetagOptions.make PreparedReflection.actual.compiler options.retag)
    (config options remaining span).access (config options remaining span).projection table pointers choice

theorem exists_context (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false) : Nonempty (Context options remaining span) := by
  have fields := actual_fields options () remaining span
  obtain ⟨pointers, table, globals, choice, construction, arithmetic, resolve, ensure, synchronize⟩ := fields.retagConstruction
  have source : TypedRetagFields.SourceFields (config options remaining span).retag
      ReferenceMetadataFacts.prepared (config options remaining span).access
      (config options remaining span).projection table pointers choice := by
    constructor
    · rw [construction]; rfl
    · rw [construction]; rfl
    · rw [construction]; rfl
    · exact fields.retagLog
    · rw [fields.retagPrecise, precise]
    · rw [fields.retagImplicit, implicitWrites]
    · rw [construction]; rfl
    · rw [construction]; rfl
    · rw [construction]; rfl
  exact ⟨⟨pointers, table, choice, source, arithmetic, resolve, globals, ensure, synchronize, construction⟩⟩

theorem bool_layout_exact : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1 ∧
    RootCompilerFacts.boolLayout.layout.align.abi = Align.ONE ∧
    RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel

theorem bool_freeze_query : CompilerFacts.boolean RootMetadataQueries.context 0 "is_freeze" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  simp only [RootMetadataQueries.context_node]
  with_unfolding_all rfl

theorem bool_freeze (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span) :
    (config options remaining span).retag.typeIsFreeze RootCompilerFacts.boolLayout.ty = pure true := by
  rw [ctx.construction]
  unfold EvalRetagMachine.hooks
  dsimp only
  have ty : RootCompilerFacts.boolLayout.ty = 0 := by decide +kernel
  rw [ty, show ReferenceMetadataFacts.prepared.context = RootMetadataQueries.context from rfl, bool_freeze_query]
  with_unfolding_all rfl

theorem bool_size (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout) :
    (config options remaining span).retag.sizeAndAlign place = pure (some (Size.ofBytes 1, Align.ONE)) := by
  rw [ctx.source.sizing]
  funext state
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp only [layout, bool_layout_exact.2.2,  ↓reduceIte, bool_layout_exact.1,
    bool_layout_exact.2.1]

end
end DuplicatePrefix.ActualRetagContext
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ActualRetagContext.exists_context,
      ``DuplicatePrefix.ActualRetagContext.bool_freeze,
      ``DuplicatePrefix.ActualRetagContext.bool_size] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved actual retag context dependency {dependency}"
