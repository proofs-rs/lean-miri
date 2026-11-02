import duplicate_prefix.ActualReferenceContext
import duplicate_prefix.LayoutLookupProof

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.ActualReferenceMetadata
open Miri Miri.ABI Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext

noncomputable abbrev reference := RootCompilerFacts.sliceLayout
noncomputable abbrev pointee := ProjectionMetadataFacts.sliceLayout

theorem reference_ty : reference.ty = 3 := by
  exact congrArg Prod.fst RootCompilerFacts.slice_layout_shape

theorem pointee_ty : pointee.ty = 4 := ProjectionMetadataFacts.slice_layout_shape.1

theorem pointee_layout : CompilerFacts.layoutOf RootMetadataQueries.context 4 = .ok pointee := by
  unfold CompilerFacts.layoutOf
  erw [LayoutLookupProof.indexed_lookup_eq]
  rw [ProjectionMetadataFacts.slice_layout_eq]
  rfl

theorem reference_queries (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (pointers : RootPointers) :
    TypedRetagFields.ReferenceQueries (adapted options remaining span pointers) reference.ty pointee.ty := by
  rw [reference_ty, pointee_ty]
  apply TypedRetagFields.adapted_reference_queries
  · exact RootMetadataQueries.mutable_slice_shape
  · exact RootMetadataQueries.mutable_slice_reference
  · exact RootMetadataQueries.slice_unpin
  · exact RootMetadataQueries.slice_unsafe_unpin
  · exact RootMetadataQueries.slice_freeze

theorem reference_sized : reference.layout.isSized = true := by decide +kernel

theorem reference_repr : ∃ (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size),
    reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset) := by
  with_unfolding_all exact ⟨_, _, _, _, _, rfl⟩

theorem visitor_metadata (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).validity.target = (config options remaining span).access.runtime ∧
    (config options remaining span).validity.metadataTail () 4 = pure .sliceOrStr ∧
    (config options remaining span).validity.opsemInhabited () 4 = pure true ∧
    (config options remaining span).validity.typeName () 3 = pure "&mut [u8]" ∧
    (config options remaining span).validity.classify () 3 = pure (.reference true) := by
  obtain ⟨pointers, table, discr, validity⟩ := (actual_fields options () remaining span).validity
  have target : (config options remaining span).validity.target = (config options remaining span).access.runtime := by
    rw [validity]; rfl
  have tail : (config options remaining span).validity.metadataTail =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).metadataTail := by
    rw [validity]; rfl
  have inhabit : (config options remaining span).validity.opsemInhabited =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).opsemInhabited := by
    rw [validity]; rfl
  have name : (config options remaining span).validity.typeName =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).typeName := by
    rw [validity]; rfl
  have kind : (config options remaining span).validity.classify =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).classify := by
    rw [validity]; rfl
  refine ⟨target, ?_, ?_, ?_, ?_⟩
  · rw [tail]; exact ReferenceMetadataFacts.hooks_metadata_tail _ ()
  · rw [inhabit]
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [show ReferenceMetadataFacts.prepared.context = RootMetadataQueries.context from rfl,
      ReferenceMetadataFacts.slice_inhabited]
    with_unfolding_all rfl
  · rw [name]; exact ReferenceMetadataFacts.hooks_reference_name _ ()
  · rw [kind]; exact ReferenceMetadataFacts.hooks_reference_kind _ ()

theorem visitor_target (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).validity.target.base.pointerWidth = .w64 ∧
    (config options remaining span).validity.target.pointerSize = Size.ofBytes 8 := by
  rw [(visitor_metadata options remaining span).1, actual_access_runtime]
  exact ⟨rfl, rfl⟩

end DuplicatePrefix.ActualReferenceMetadata
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ActualReferenceMetadata.reference_queries,
      ``DuplicatePrefix.ActualReferenceMetadata.pointee_layout,
      ``DuplicatePrefix.ActualReferenceMetadata.visitor_metadata,
      ``DuplicatePrefix.ActualReferenceMetadata.visitor_target,
      ``DuplicatePrefix.ActualReferenceMetadata.reference_repr] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata dependency {dependency}"
