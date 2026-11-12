import Miri.Input.StructuralSized
import Miri.Input.GenericSubstitution

/-! Sizedness over source type expressions, including ADT instantiations which
have no material TypeId. The ADT callback supplies the original declaration
kind and field templates; it must validate their complete field domains. No
layout or compiler-computed sizedness constraint is accepted as evidence. -/
namespace Miri.Input.TermSized
open GenericSubstitution

structure Hooks where
  sourceAdt : DefinitionIdentity → Except String (AdtKind × DefinitionTemplate)
  normalizeAlias : Nat → Term → Except String Term

private def arguments : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ arguments tail

/-- Pinned trait structural candidate and ADT trailing-field constraint, applied
before runtime type interning. Unknown source constructors fail explicitly. -/
def query (hooks : Hooks) (kind : StructuralSized.TraitKind) :
    Nat → Term → Except String Bool
  | 0, _ => .error "term Sized recursion exhausted"
  | fuel + 1, term => do
    match term with
    | .atom .type "str" _ => pure (kind == .metaSized)
    | .atom .type tag _ =>
      if #["bool", "char", "int", "uint", "float", "never"].contains tag then return true
      throw "unknown source atom in term Sized"
    | .node .type "slice" .. | .node .type "dynamic" .. => pure (kind == .metaSized)
    | .node .type "tuple" _ children =>
      match (arguments children).back? with
      | none => pure true
      | some tail => query hooks kind fuel tail
    | .node .type "unsafe_binder" .. =>
      throw "term Sized trait candidate requires unsafe-binder relation semantics"
    | .node .type tag .. =>
      if #["reference", "raw_pointer", "array", "pattern", "function_pointer"].contains tag then
        return true
      throw "unknown source node in term Sized"
    | .definition .type "foreign" .. => pure false
    | .definition .type "adt" definition children =>
      let (sourceKind, template) ← hooks.sourceAdt definition
      let args := arguments children
      template.checkArguments args
      if sourceKind != .structKind then return true
      let fields := template.fields.filter (·.variantIndex == 0)
      unless fields.size == template.fields.size do throw "struct Sized source has nonzero variant field"
      for (field, index) in fields.zipIdx do
        unless field.fieldIndex == index do throw "struct Sized source field domain is not dense"
      match fields.back? with
      | none => pure true
      | some tail => query hooks kind fuel (← instantiate (fuel + 1) args tail.expression)
    | .definition .type tag .. =>
      if tag.startsWith "alias_" then
        let normalized ← hooks.normalizeAlias fuel term
        if normalized == term then throw "term Sized alias remained unresolved"
        return ← query hooks kind fuel normalized
      if #["function_definition", "closure", "coroutine_closure", "coroutine", "coroutine_witness"].contains tag then
        return true
      throw "unknown source definition in term Sized"
    | _ => throw "term Sized requires a concrete type expression"

end Miri.Input.TermSized
