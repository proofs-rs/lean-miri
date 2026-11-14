import Miri.Input.TraitSelection.StructuralCopyClone

/-! Source candidate-assembly component checks. No builtin candidate does not
mean no trait implementation: primitives/arrays/ref use core source impls. -/
open Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def u8 : Term := .atom .type "uint" "u8"
private def u16 : Term := .atom .type "uint" "u16"
private def tuple : Term := .node .type "tuple" "" (.ofArray #[u8,u16])
private def function : Term := .definition .type "function_definition" ⟨0,1⟩ (.ofArray #[
  .binder #[] (.node .aggregate "arguments" "" .nil)])
private def pointer : Term := .node .type "function_pointer" "" (.ofArray #[
  .binder #[] (.node .aggregate "signature" "" (.ofArray #[u8,u16]))])
private def result : Except String (Option (Array Term)) → String
  | .error _ => "unsupported"
  | .ok none => "no_builtin"
  | .ok (some fields) => toString fields.size
example : result (StructuralCopyClone.query 30 u8) = "no_builtin" := by decide +kernel
example : result (StructuralCopyClone.query 30 function) = "0" := by decide +kernel
example : result (StructuralCopyClone.query 30 pointer) = "0" := by decide +kernel
example : result (StructuralCopyClone.query 30 tuple) = "2" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.node .type "tuple" "" .nil)) = "0" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.definition .type "adt" ⟨0,2⟩ .nil)) = "no_builtin" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.node .type "array" "" (.ofArray #[u8,.atom .constant "value" ""]))) = "no_builtin" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.node .type "pattern" "" (.ofArray #[
    .node .type "raw_pointer" "immutable" (.ofArray #[u8]),.atom .aggregate "pattern_not_null" ""]))) = "1" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.definition .type "closure" ⟨0,3⟩ (.ofArray #[u8,pointer,tuple]))) = "1" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.definition .type "coroutine_closure" ⟨0,3⟩ (.ofArray #[u8,pointer,tuple,pointer]))) = "1" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.definition .type "closure" ⟨0,3⟩ (.ofArray #[tuple]))) = "unsupported" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.definition .type "coroutine" ⟨0,4⟩ .nil)) = "unsupported" := by decide +kernel
example : result (StructuralCopyClone.query 30 (.node .type "function_pointer" "" .nil)) = "unsupported" := by decide +kernel
