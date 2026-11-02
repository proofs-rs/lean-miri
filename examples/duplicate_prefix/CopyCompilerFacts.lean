import duplicate_prefix.RootCompilerFacts
import duplicate_prefix.LayoutLookupProof

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.CopyCompilerFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter

private def checkedOk {Error Value : Type} : (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {Error Value : Type} (result : Except Error Value) (supported : result.isOk = true) :
    result = .ok (checkedOk result supported) := by
  cases result with
  | ok value => rfl
  | error reason => cases supported

theorem byte_layout_supported : (PreparedReflection.actual.runtime.lookup 1).isOk = true := by decide +kernel
theorem source_pointer_layout_supported : (PreparedReflection.actual.runtime.lookup 9).isOk = true := by decide +kernel
theorem dest_pointer_layout_supported : (PreparedReflection.actual.runtime.lookup 8).isOk = true := by decide +kernel

def byteLayout : LocalLayout := checkedOk (PreparedReflection.actual.runtime.lookup 1) byte_layout_supported
def sourcePointerLayout : LocalLayout := checkedOk (PreparedReflection.actual.runtime.lookup 9) source_pointer_layout_supported
def destPointerLayout : LocalLayout := checkedOk (PreparedReflection.actual.runtime.lookup 8) dest_pointer_layout_supported

theorem byte_layout_eq : PreparedReflection.actual.runtime.lookup 1 = .ok byteLayout := checkedOk_eq _ _
theorem source_pointer_layout_eq : PreparedReflection.actual.runtime.lookup 9 = .ok sourcePointerLayout := checkedOk_eq _ _
theorem dest_pointer_layout_eq : PreparedReflection.actual.runtime.lookup 8 = .ok destPointerLayout := checkedOk_eq _ _

theorem byte_layout_shape : byteLayout.ty = 1 ∧ byteLayout.layout.size = Size.ofBytes 1 ∧
    byteLayout.layout.align.abi = Align.ONE := by decide +kernel

def initializedScalar (layout : LocalLayout) : Bool :=
  match layout.layout.backendRepr with | .Scalar (.Initialized ..) => true | _ => false

theorem primitive_layouts_initialized : initializedScalar byteLayout = true ∧
    initializedScalar sourcePointerLayout = true ∧ initializedScalar destPointerLayout = true ∧
    initializedScalar RootCompilerFacts.usizeLayout = true := by decide +kernel

theorem initialized_scalar_exists (layout : LocalLayout) (supported : initializedScalar layout = true) :
    ∃ primitive range, layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)) := by
  cases reprEq : layout.layout.backendRepr with
  | Scalar scalar =>
    cases scalar with
    | Initialized => exact ⟨_, _, rfl⟩
    | Union => simp [initializedScalar, reprEq] at supported
  | _ => simp [initializedScalar, reprEq] at supported

theorem copy_helper_locals : RootBody.reflected.copyHelper.body.locals =
    #[2,9,8,5,2,0,2,45,9,46,8,5,5,5,9,8,5] := by rfl

theorem compiler_byte_layout : CompilerFacts.layoutOf
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 1 = .ok byteLayout := by
  unfold CompilerFacts.layoutOf
  erw [LayoutLookupProof.indexed_lookup_eq]
  decide +kernel

theorem compiler_source_pointer_layout : CompilerFacts.layoutOf
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 9 = .ok sourcePointerLayout := by
  unfold CompilerFacts.layoutOf
  erw [LayoutLookupProof.indexed_lookup_eq]
  decide +kernel

theorem compiler_dest_pointer_layout : CompilerFacts.layoutOf
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 8 = .ok destPointerLayout := by
  unfold CompilerFacts.layoutOf
  erw [LayoutLookupProof.indexed_lookup_eq]
  decide +kernel

theorem compiler_usize_layout : CompilerFacts.layoutOf
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 5 = .ok RootCompilerFacts.usizeLayout := by
  unfold CompilerFacts.layoutOf
  erw [LayoutLookupProof.indexed_lookup_eq]
  decide +kernel

#print axioms compiler_byte_layout

#print axioms byte_layout_shape
#print axioms primitive_layouts_initialized
#print axioms copy_helper_locals
open Lean Elab Command in
run_cmd do
  for declaration in [``compiler_byte_layout, ``compiler_source_pointer_layout, ``compiler_dest_pointer_layout, ``compiler_usize_layout, ``byte_layout_supported, ``source_pointer_layout_supported, ``dest_pointer_layout_supported,
      ``byte_layout_eq, ``source_pointer_layout_eq, ``dest_pointer_layout_eq, ``byte_layout_shape,
      ``primitive_layouts_initialized, ``initialized_scalar_exists, ``copy_helper_locals] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end
end DuplicatePrefix.CopyCompilerFacts
