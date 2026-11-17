import duplicate_prefix.RootReferenceValidator
import duplicate_prefix.NestedConstruction
namespace DuplicatePrefix.RootReferenceInfo
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def layout (shared : Bool) : LocalLayout := if shared then SharedReferenceMetadata.sharedLayout else ActualReferenceMetadata.reference
def mutability (shared : Bool) : MIR.Mutability := if shared then .Not else .Mut
def mode (shared : Bool) : RetagPolicy.RetagMode := if shared then .Default else .TwoPhase
def policy (shared : Bool) : RetagPolicy.NewPermission := if shared then NestedConstruction.sharedPolicy false else NestedConstruction.twoPhasePolicy
def initial (shared : Bool) : Tree.LocationState := if shared then NestedConstruction.frozenRead else NestedConstruction.mutableRead
def name (shared : Bool) : String := if shared then "&[u8]" else "&mut [u8]"

structure Info (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span) (shared : Bool) : Prop where
  sized : (layout shared).layout.isSized = true
  readable : ∃ pa pb ra rb offset, (layout shared).layout.backendRepr = .ScalarPair
    (a := .Initialized (value := pa) (validRange := ra)) (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset)
  protection : (policy shared).protector = none
  associated : (initial shared).permission.associatedAccess = some .Read
  initialState : RetagPolicy.initialLocationState (policy shared) true = .ok (initial shared)
  created : RetagPolicy.create ⟨true,true,true⟩ (if mutability shared == .Mut then .Mutable else .Shared)
    (mode shared) ⟨false,false⟩ = some (policy shared)
  shape : (adapted options remaining span ctx.pointers).typeShape (layout shared).ty = pure .reference
  pointeeQuery : (adapted options remaining span ctx.pointers).referencePointee (layout shared).ty =
    pure (ProjectionMetadataFacts.sliceLayout.ty,mutability shared)
  unpin : (adapted options remaining span ctx.pointers).isUnpin ProjectionMetadataFacts.sliceLayout.ty = pure true
  unsafeUnpin : (adapted options remaining span ctx.pointers).isUnsafeUnpin ProjectionMetadataFacts.sliceLayout.ty = pure true
  frozen : (adapted options remaining span ctx.pointers).typeIsFreeze ProjectionMetadataFacts.sliceLayout.ty = pure true
  dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context (layout shared).ty true =
    .ok (some ProjectionMetadataFacts.sliceLayout.ty)
  named : (config options remaining span).validity.typeName () (layout shared).ty = pure (name shared)
  classified : (config options remaining span).validity.classify () (layout shared).ty = pure (.reference (mutability shared == .Mut))

theorem facts (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span) (shared : Bool) : Info options remaining span ctx shared := by
  have mutableQueries := ActualReferenceMetadata.reference_queries options remaining span ctx.pointers
  have sharedQueries := SharedReferenceMetadata.adapted_queries
    PreparedReflection.actual.compiler.lifecycle.calls.runtime (config options remaining span).access
    (config options remaining span).validity.projection (config options remaining span).validity.vtable
    ctx.pointers () (config options remaining span).retag
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨target,tail,inhabited,named3,kind3⟩ := ActualReferenceMetadata.visitor_metadata options remaining span
  obtain ⟨pointers,table,discriminant,validity⟩ := fields.validity
  have nameField : (config options remaining span).validity.typeName =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).typeName := by
    rw [validity];rfl
  have kindField : (config options remaining span).validity.classify =
      (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared (config options remaining span).validity).classify := by
    rw [validity];rfl
  cases shared with
  | false =>
    refine ⟨ActualReferenceMetadata.reference_sized,ActualReferenceMetadata.reference_repr,rfl,by decide,
      NestedConstruction.mutable_two_phase_initial,NestedConstruction.mutable_two_phase_policy,
      mutableQueries.shape,mutableQueries.pointee_eq,mutableQueries.unpin,mutableQueries.unsafeUnpin,mutableQueries.freeze,?_,?_,?_⟩
    · rw [layout,if_neg (by decide),ActualReferenceMetadata.reference_ty,ProjectionMetadataFacts.slice_layout_shape.1]
      exact RootMetadataQueries.mutable_slice_dereference
    · simpa only [layout,name,Bool.false_eq_true,↓reduceIte,ActualReferenceMetadata.reference_ty] using named3
    · simpa only [layout,mutability,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,ActualReferenceMetadata.reference_ty] using kind3
  | true =>
    refine ⟨SharedReferenceMetadata.shared_layout_sized,SharedReferenceMetadata.shared_layout_readable,rfl,by decide,
      NestedConstruction.shared_initial false,NestedConstruction.shared_default_policy,
      ?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [layout,adapted,ReferenceMetadataFacts.prepared,↓reduceIte,SharedReferenceMetadata.shared_layout_type] using sharedQueries.1
    · simpa only [layout,mutability,adapted,ReferenceMetadataFacts.prepared,Bool.false_eq_true,↓reduceIte,SharedReferenceMetadata.shared_layout_type,ProjectionMetadataFacts.slice_layout_shape.1] using sharedQueries.2.1
    · exact sharedQueries.2.2.1
    · exact sharedQueries.2.2.2.1
    · exact sharedQueries.2.2.2.2
    · rw [layout,if_pos rfl,SharedReferenceMetadata.shared_layout_type,ProjectionMetadataFacts.slice_layout_shape.1]
      exact SharedReferenceMetadata.shared_dereference
    · rw [nameField]
      exact SharedReferenceMetadata.hooks_shared_name _ ()
    · rw [kindField]
      exact SharedReferenceMetadata.hooks_shared_kind _ ()

#print axioms facts
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``facts) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.RootReferenceInfo
