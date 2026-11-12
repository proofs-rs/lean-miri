import Miri.Input.AdtDeclaration

/-! Pinned next-solver structural_traits.rs auto-trait constituents and
trait_goals.rs unsafe-field guard. Source impl disqualification is performed
by Fulfill BEFORE this provider. No runtime type/layout index is consulted.
`none` means no structural candidate, never a negative trait proof by itself. -/
namespace Miri.Input.TraitSelection.StructuralAuto
open GenericSubstitution

abbrev SourceAdt := DefinitionIdentity → Except String (AdtDeclaration.Material × DefinitionTemplate)
private def array : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ array tail
private def types (values : Array Term) : Except String (Array Term) := do
  for value in values do
    unless value.sort == .type do throw "auto-trait constituent is not a type"
  pure values
private def captures (synthetics trailing : Nat) (arguments : Terms) : Except String (Array Term) := do
  let arguments := array arguments
  unless arguments.size >= synthetics do throw "auto-trait closure source synthetics absent"
  let _ ← types ((arguments.toList.drop (arguments.size - synthetics)).toArray)
  let some tuple := arguments[arguments.size - trailing]? | throw "auto-trait source capture tuple absent"
  let .node .type "tuple" _ _ := tuple | throw "auto-trait upvars are not a tuple"
  pure #[tuple]

def query (sourceAdt : SourceAdt) (unsafeTrait : Bool) :
    Nat → Term → Except String (Option (Array Term))
  | 0, _ => .error "auto-trait constituent traversal exhausted"
  | fuel + 1, self => do
    match self with
    | .atom .type tag _ =>
      if tag == "str" then return some #[.node .type "slice" "" (.ofArray #[.atom .type "uint" "u8"])]
      unless ["uint", "int", "bool", "float", "char", "never"].contains tag do
        throw "unknown auto-trait source primitive"
      pure (some #[])
    | .node .type tag _ children =>
      match tag, children with
      | "raw_pointer", .cons element .nil
      | "slice", .cons element .nil
      | "reference", .cons _ (.cons element .nil)
      | "array", .cons element (.cons _ .nil)
      | "pattern", .cons element (.cons _ .nil) => pure (some (← types #[element]))
      | "tuple", children => pure (some (← types (array children)))
      | "function_pointer", .cons _ .nil => pure (some #[])
      | "dynamic", _ => pure none
      | "unsafe_binder", _ => throw "auto-trait unsafe binder requires universe-aware constituent instantiation"
      | _, _ => throw "unknown or malformed auto-trait source structure"
    | .definition .type tag definition arguments =>
      match tag with
      | "function_definition" => pure (some #[])
      | "closure" => pure (some (← captures 3 1 arguments))
      | "coroutine_closure" => pure (some (← captures 4 2 arguments))
      | "adt" =>
        let (material, template) ← sourceAdt definition
        material.validate template
        let arguments := array arguments
        let instantiated ← template.instantiateType (fuel + 1) arguments
        unless instantiated = self do throw "auto-trait ADT source template identity differs from Self"
        if unsafeTrait && material.hasUnsafeFields then return none
        if material.isPhantomData then
          let some argument := arguments[0]? | throw "PhantomData source type argument absent"
          return some (← types #[argument])
        let fields ← template.fields.mapM fun field => instantiate fuel arguments field.expression
        pure (some (← types fields))
      | "foreign" => throw "foreign auto-trait candidate requires default-bound source context"
      | "coroutine" | "coroutine_witness" =>
        throw "auto-trait coroutine requires source hidden-type binders and movability"
      | "alias_projection_rigid" | "alias_inherent_rigid" | "alias_free_rigid" => pure none
      | _ => throw "auto-trait opaque/alias requires normalization and hidden-type source constraints"
    | .parameter .type _ | .placeholder .type .. => pure none
    | _ => throw "auto-trait source Self is not a type"

end Miri.Input.TraitSelection.StructuralAuto
