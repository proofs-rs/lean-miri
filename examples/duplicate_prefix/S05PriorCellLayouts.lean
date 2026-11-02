import duplicate_prefix.S05PriorCellMetadata
namespace DuplicatePrefix.PriorCellMetadata
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private def checkedLayout {Error Value : Type} : (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

private theorem supported_shared : (actual.runtime.lookup 6).isOk = true := by decide +kernel
private theorem supported_slice_ref : (actual.runtime.lookup 7).isOk = true := by decide +kernel
private theorem supported_slice : (actual.runtime.lookup 8).isOk = true := by decide +kernel
private theorem supported_byte : (actual.runtime.lookup 4).isOk = true := by decide +kernel

noncomputable def sharedLayout : LocalLayout := checkedLayout (actual.runtime.lookup 6) supported_shared
noncomputable def sliceReferenceLayout : LocalLayout := checkedLayout (actual.runtime.lookup 7) supported_slice_ref
noncomputable def sliceLayout : LocalLayout := checkedLayout (actual.runtime.lookup 8) supported_slice
noncomputable def byteLayout : LocalLayout := checkedLayout (actual.runtime.lookup 4) supported_byte

theorem shared_layout_query : CompilerFacts.layoutOf facts.context 6 = .ok sharedLayout := by
  rw [compiler_layout_lookup]
  decide +kernel

theorem slice_reference_layout_query : CompilerFacts.layoutOf facts.context 7 = .ok sliceReferenceLayout := by
  rw [compiler_layout_lookup]
  decide +kernel

theorem slice_layout_query : CompilerFacts.layoutOf facts.context 8 = .ok sliceLayout := by
  rw [compiler_layout_lookup]
  decide +kernel

theorem byte_layout_query : CompilerFacts.layoutOf facts.context 4 = .ok byteLayout := by
  rw [compiler_layout_lookup]
  decide +kernel

theorem layout_type_ids : sharedLayout.ty = 6 ∧ sliceReferenceLayout.ty = 7 ∧
    sliceLayout.ty = 8 ∧ byteLayout.ty = 4 := by decide +kernel

theorem slice_geometry : sliceLayout.layout.isSized = false ∧
    byteLayout.layout.size = Size.ofBytes 1 ∧ byteLayout.layout.align.abi = Align.ONE := by decide +kernel

theorem slice_freeze : CompilerFacts.boolean facts.context 8 "is_freeze" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_unpin : CompilerFacts.boolean facts.context 8 "is_unpin" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_unsafe_unpin : CompilerFacts.boolean facts.context 8 "is_unsafe_unpin" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_reference_shape : CompilerFacts.retagTypeShape facts.context 7 = .ok .reference := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_reference_deref : CompilerFacts.builtinDeref facts.context 7 true = .ok (some 8) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl
private theorem supported_bool : (actual.runtime.lookup 27).isOk = true := by decide +kernel
noncomputable def boolLayout : LocalLayout := checkedLayout (actual.runtime.lookup 27) supported_bool

theorem bool_layout_query : CompilerFacts.layoutOf facts.context 27 = .ok boolLayout := by
  rw [compiler_layout_lookup]
  decide +kernel

theorem bool_geometry : boolLayout.ty = 27 ∧ boolLayout.layout.size = Size.ofBytes 1 ∧
    boolLayout.layout.align.abi = Align.ONE := by decide +kernel

private theorem supported_u16 : (actual.runtime.lookup 18).isOk = true := by decide +kernel
noncomputable def u16Layout : LocalLayout := checkedLayout (actual.runtime.lookup 18) supported_u16

theorem u16_layout_query : CompilerFacts.layoutOf facts.context 18 = .ok u16Layout := by
  rw [compiler_layout_lookup]
  decide +kernel

theorem u16_geometry : u16Layout.ty = 18 ∧ u16Layout.layout.isSized = true ∧
    u16Layout.layout.size = Size.ofBytes 2 ∧ u16Layout.layout.align.abi = ⟨1⟩ := by decide +kernel

theorem u16_scalar : u16Layout.layout.backendRepr =
    .Scalar (.Initialized (value := .Int .I16 false) (validRange := ⟨0,65535⟩)) := by decide +kernel

/-- The exact JSON comparison remains a transparent configuration condition,
as in the fixed function's existing projection facts. -/
def NullComparator : Prop := (Lean.Json.null == Lean.Json.null) = true

open Lean Elab Command in
run_cmd do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".RuntimeMetadata.projectionParents" then some name else none
  let helper := mkIdent names.head!
  let declaration := mkIdent `slice_projection_parents
  elabCommand (← `(theorem $declaration (cmp : NullComparator) :
      $helper actual.runtime 8 = .ok #[] := by
    change (if (Lean.Json.null == Lean.Json.null) = true then _ else _) = _
    rw [cmp]
    rfl))

theorem slice_field (cmp : NullComparator) :
    actual.runtime.field sliceLayout 0 = .ok byteLayout := by
  unfold RuntimeMetadata.field
  rw [layout_type_ids.2.2.1, slice_projection_parents cmp]
  simp only [← Array.forIn_toList]
  with_unfolding_all rfl

theorem slice_dynamic_kind : EvalProjectionMachine.dynamicKind facts 8 = .ok .slice := by
  with_unfolding_all rfl

end DuplicatePrefix.PriorCellMetadata
