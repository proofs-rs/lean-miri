import Miri.Input.TraitSelection.Material
import Miri.Input.ReprMaterial

namespace Miri.Input

inductive AdtKind where
  | structKind | unionKind | enumKind
  deriving Repr, DecidableEq

namespace AdtDeclaration
open GenericSubstitution

structure FieldSafety where
  variantIndex : Nat
  fieldIndex : Nat
  isUnsafe : Bool
  fieldName : String
  deriving Repr, DecidableEq

structure Material where
  representation : ReprOptions
  kind : AdtKind
  langItem : Option String
  variantCount : Nat
  variantNames : Array String
  fields : Array FieldSafety
  deriving Repr, DecidableEq

def Material.isPhantomData (material : Material) : Bool := material.langItem == some "phantom_data"
def Material.hasUnsafeFields (material : Material) : Bool := material.fields.any (·.isUnsafe)

/-- These attributes accompany raw declaration field expressions. They must
have the same complete ordered field domain; neither table supplies query
answers for instantiated ADTs. Empty variants are represented by variantCount. -/
def Material.validate (material : Material) (template : DefinitionTemplate) : Except String Unit := do
  unless material.variantNames.size == material.variantCount do
    throw "ADT source variant name domain differs from variant count"
  unless material.kind == .enumKind || material.variantCount == 1 do
    throw "struct/union source declaration must have exactly one variant"
  if material.isPhantomData && material.kind != .structKind then
    throw "PhantomData source declaration is not a struct"
  unless material.fields.size == template.fields.size do
    throw "ADT source field safety and expression domains differ"
  let mut previous : Option (Nat × Nat) := none
  for (safety, expression) in material.fields.zip template.fields do
    unless safety.variantIndex == expression.variantIndex && safety.fieldIndex == expression.fieldIndex do
      throw "ADT source field safety identity differs from field expression"
    unless safety.variantIndex < material.variantCount do
      throw "ADT source field variant index out of bounds"
    let expected ← match previous with
      | none => pure 0
      | some (variant, next) =>
        if safety.variantIndex == variant then pure next
        else if safety.variantIndex > variant then pure 0
        else throw "ADT source fields are not in variant order"
    unless safety.fieldIndex == expected do throw "ADT source field indices are not dense"
    previous := some (safety.variantIndex, expected + 1)


end AdtDeclaration
end Miri.Input
