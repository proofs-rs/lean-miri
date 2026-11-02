import duplicate_prefix.WideValidityQueries
import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.PtrMetadataHelper
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.AsMutPtrFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ScalarValidityQueries WideValidityQueries
noncomputable section
private def checkedOk {E V : Type} : (value : Except E V) → value.isOk = true → V
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {E V : Type} (value : Except E V) (supported : value.isOk = true) :
    value = .ok (checkedOk value supported) := by
  cases value with
  | ok value => rfl
  | error error => cases supported
theorem raw_layout_supported : (PreparedReflection.actual.runtime.lookup 204).isOk = true := by decide +kernel
def rawLayout := checkedOk (PreparedReflection.actual.runtime.lookup 204) raw_layout_supported
theorem raw_layout_eq : PreparedReflection.actual.runtime.lookup 204 = .ok rawLayout := checkedOk_eq _ _
theorem raw_type : rawLayout.ty = 204 := by with_unfolding_all rfl
theorem raw_sized : rawLayout.layout.isSized = true := by with_unfolding_all rfl
theorem raw_size : rawLayout.layout.size = Size.ofBytes 16 := by with_unfolding_all rfl
theorem raw_data : rawLayout.layout = PtrMetadataHelper.rawLayout.layout := by with_unfolding_all rfl
theorem raw_readable : ∃ pa pb ra rb offset, rawLayout.layout.backendRepr =
    .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset) := by
  rw [raw_data]
  exact PtrMetadataHelper.raw_readable
theorem raw_no_padding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false rawLayout = .ok false := by decide +kernel
theorem raw_slice_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 204 = .ok (.rawPointer 4 false) := by
  unfold CompilerFactAdapters.validityKind
  unfold_raw_validity_helpers
  dsimp only
  have nodes (id : TypeId) : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node id =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node id :=
    RootMetadataQueries.context_node id
  simp only [nodes]
  change (do
    let sized ← CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 4 "is_sized"
    pure (ValidityVisitor.TypeKind.rawPointer 4 sized)) = .ok (ValidityVisitor.TypeKind.rawPointer 4 false)
  rw [slice_unsized]
  rfl
theorem hooks_raw_slice_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 204 = pure (.rawPointer 4 false) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [raw_slice_kind]
  with_unfolding_all rfl

theorem hooks_raw_slice_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 204 = pure "*mut [u8]" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 204 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 204 :=
    RootMetadataQueries.context_node 204
  rw [node]
  with_unfolding_all rfl

theorem context_raw_layout : CompilerFacts.layoutOf RootMetadataQueries.context 204 = .ok rawLayout := by
  unfold CompilerFacts.layoutOf
  rw [show RootMetadataQueries.context.runtime.lookup 204 = PreparedReflection.actual.runtime.lookup 204 from
    LayoutLookupProof.indexed_lookup_eq PreparedReflection.actual.runtime none 204]
  rw [raw_layout_eq]
  rfl

theorem raw_builtin_deref : CompilerFacts.builtinDeref RootMetadataQueries.context 204 true = .ok (some 4) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [RootMetadataQueries.context_node]
  with_unfolding_all rfl

theorem compiler_raw_deref {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U)
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).builtinDeref choice 204 = pure (some 4) := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = RootMetadataQueries.context from rfl,
    raw_builtin_deref]
  unfold_internal ".CompilerExecutionProviders.liftResult"
  unfold_internal ".CompilerExecutionProviders.query"
  rfl

theorem cast_raw_info : CompilerFactAdapters.castTypeInfo
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 204 = .ok (.rawPointer 4) := by decide +kernel

theorem cast_thin_info : CompilerFactAdapters.castTypeInfo
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 8 = .ok (.rawPointer 1) := by decide +kernel

theorem raw_retag_shape : CompilerFacts.retagTypeShape RootMetadataQueries.context 204 =
    .ok ⟨false, false, true, false⟩ := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_fact_helpers
  simp only [RootMetadataQueries.context_node]
  with_unfolding_all rfl

theorem body_locals : HelperCompilerFacts.asMutPtrBody.body.locals = #[8,3,8,204,204] := by with_unfolding_all rfl

def block := HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]'(by decide +kernel)

theorem body_block : HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]? = some block := by
  with_unfolding_all rfl

theorem statement_kinds : block.statements.map (·.kind) = #[
    .StorageLive 2, .StorageLive 3, .StorageLive 4,
    .Assign ⟨4,#[]⟩ (.RawPtr .Mut ⟨1,#[.Deref]⟩),
    .Assign ⟨3,#[]⟩ (.Use (.Copy ⟨4,#[]⟩) .Yes),
    .Assign ⟨2,#[]⟩ (.Cast .PtrToPtr (.Move ⟨3,#[]⟩) 8),
    .Assign ⟨0,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes),
    .StorageDead 4, .StorageDead 3, .StorageDead 2] := by with_unfolding_all rfl

theorem terminator_return : block.terminator.kind = .Return := by with_unfolding_all rfl

theorem normal_block : block.cleanup = false := by with_unfolding_all rfl

open Lean Elab Command in
run_cmd do
  for declaration in [``context_raw_layout, ``raw_builtin_deref, ``compiler_raw_deref, ``cast_raw_info, ``cast_thin_info, ``raw_retag_shape, ``body_locals, ``body_block, ``statement_kinds, ``terminator_return, ``normal_block, ``raw_layout_eq, ``raw_type, ``raw_sized, ``raw_size, ``raw_data, ``raw_readable,
      ``raw_no_padding, ``raw_slice_kind, ``hooks_raw_slice_kind, ``hooks_raw_slice_name] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end
end DuplicatePrefix.AsMutPtrFacts
