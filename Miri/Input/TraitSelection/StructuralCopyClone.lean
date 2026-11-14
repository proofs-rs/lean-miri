import Miri.Input.TraitSelection.Material

namespace Miri.Input.TraitSelection.StructuralCopyClone
open GenericSubstitution

/-! Source candidate assembly, pinned `assembly/structural_traits.rs`,
`instantiate_constituent_tys_for_copy_clone_trait`. `none` means no BUILTIN
candidate: primitive/array/reference implementations live in raw core impls.
It never means that the trait goal itself has no solution. -/
private def array : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ array tail

private def captured (synthetics syntheticOffset : Nat) (arguments : Terms) : Except String (Array Term) := do
  let arguments := array arguments
  unless arguments.size >= synthetics do throw "closure synthetic source arguments absent"
  unless (arguments.toList.drop (arguments.size - synthetics)).all (·.sort == .type) do
    throw "closure synthetic source argument is not a type"
  let some capture := arguments[arguments.size - syntheticOffset]?
    | throw "closure capture tuple source absent"
  match capture with
  | .node .type "tuple" _ fields =>
    for field in array fields do
      unless field.sort == .type do throw "closure capture field is not a type"
    pure #[capture]
  | _ => throw "closure source upvars are not a tuple type"

def query : Nat → Term → Except String (Option (Array Term))
  | 0, _ => .error "Copy/Clone constituent traversal exhausted"
  | _fuel + 1, term => do
    match term with
    | .definition .type tag _ children =>
      match tag with
      | "function_definition" =>
        match children with
        | .cons (.binder _ (.node .aggregate "arguments" _ _)) .nil => pure (some #[])
        | _ => throw "malformed source function-definition arguments"
      | "closure" => pure (some (← captured 3 1 children))
      | "coroutine_closure" => pure (some (← captured 4 2 children))
      | "adt" | "foreign" => pure none
      | "coroutine" => throw "coroutine Copy/Clone requires source movability and coroutine_clone feature"
      | "coroutine_witness" => throw "coroutine witness Copy/Clone requires raw hidden-type binders"
      | "alias_projection_rigid" | "alias_inherent_rigid" | "alias_opaque_rigid" | "alias_free_rigid" => pure none
      | _ => throw "Copy/Clone source alias requires normalization"
    | .atom .type tag _ =>
      unless ["uint", "int", "bool", "float", "char", "never", "str"].contains tag do
        throw "unknown Copy/Clone source primitive"
      pure none
    | .node .type tag _ children =>
      match tag, children with
      | "function_pointer", .cons (.binder _ (.node .aggregate "signature" _ types)) .nil =>
        let types := array types
        unless !types.isEmpty && types.all (·.sort == .type) do throw "malformed source function signature types"
        pure (some #[])
      | "pattern", .cons inner (.cons _ .nil) =>
        unless inner.sort == .type do throw "pattern Copy/Clone constituent is not a type"
        pure (some #[inner])
      | "tuple", children =>
        let children := array children
        for child in children do
          unless child.sort == .type do throw "tuple Copy/Clone constituent is not a type"
        pure (some children)
      | "raw_pointer", .cons _ .nil
      | "reference", .cons _ (.cons _ .nil)
      | "array", .cons _ (.cons _ .nil)
      | "slice", .cons _ .nil
      | "unsafe_binder", .cons _ .nil => pure none
      | "dynamic", _ => pure none
      | _, _ => throw "unknown or malformed Copy/Clone source structure"
    | .parameter .type _ | .placeholder .type .. => pure none
    | _ => throw "Copy/Clone constituent source requires a type"

end Miri.Input.TraitSelection.StructuralCopyClone
