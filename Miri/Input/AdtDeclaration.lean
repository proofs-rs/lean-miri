import Miri.Input.TraitSelection.Material
import Miri.Input.ReprMaterial

namespace Miri.Input

inductive AdtKind where
  | structKind | unionKind | enumKind
  deriving Repr, DecidableEq

namespace AdtDeclaration
open GenericSubstitution

inductive ConstructorKind where
  | function | constant
  deriving Repr, DecidableEq

structure Constructor where
  kind : ConstructorKind
  definition : DefinitionIdentity
  deriving Repr, DecidableEq

inductive Discriminant where
  | explicit (definition : DefinitionIdentity)
  | relative (distance : Nat)
  deriving Repr, DecidableEq

structure Variant where
  definition : DefinitionIdentity
  constructor : Option Constructor
  name : String
  discriminant : Discriminant
  fieldCount : Nat
  flagsBits : Nat
  deriving Repr, DecidableEq

structure FieldSafety where
  variantIndex : Nat
  fieldIndex : Nat
  isUnsafe : Bool
  fieldName : String
  definition : DefinitionIdentity
  /-- Public is `none`; a restricted visibility retains its defining module. -/
  visibility : Option DefinitionIdentity
  /-- Spans do not enter stable hashes; the restriction's defining module does. -/
  mutationRestriction : Option DefinitionIdentity
  defaultValue : Option DefinitionIdentity
  deriving Repr, DecidableEq

structure Material where
  representation : ReprOptions
  flagsBits : Nat
  langItem : Option String
  variants : Array Variant
  fields : Array FieldSafety
  deriving Repr, DecidableEq

def Material.kind (material : Material) : AdtKind :=
  if material.flagsBits &&& 1 != 0 then .enumKind
  else if material.flagsBits &&& 2 != 0 then .unionKind else .structKind
def Material.variantCount (material : Material) : Nat := material.variants.size
def Material.variantNames (material : Material) : Array String := material.variants.map (·.name)
def Material.isPhantomData (material : Material) : Bool := material.langItem == some "phantom_data"
def Material.hasUnsafeFields (material : Material) : Bool := material.fields.any (·.isUnsafe)

/-- These attributes accompany raw declaration field expressions. They must
have the same complete ordered field domain; neither table supplies query
answers for instantiated ADTs. Empty variants retain their own raw records. -/
def Material.validateRaw (material : Material) : Except String Unit := do
  unless material.flagsBits < 2^15 && [1,2,4].contains (material.flagsBits &&& 7) do
    throw "ADT source flags have an invalid declaration kind or unknown bits"
  unless material.kind == .enumKind || material.variantCount == 1 do
    throw "struct/union source declaration must have exactly one variant"
  if material.isPhantomData && material.kind != .structKind then
    throw "PhantomData source declaration is not a struct"
  let mut seenVariants : Array DefinitionIdentity := #[]
  for (variant,index) in material.variants.zipIdx do
    unless !seenVariants.contains variant.definition do throw "duplicate raw variant definition identity"
    seenVariants := seenVariants.push variant.definition
    unless variant.flagsBits < 2 do throw "unknown raw variant flag bits"
    unless (material.fields.filter (·.variantIndex == index)).size == variant.fieldCount do
      throw "raw variant field count differs from its ordered field domain"
    if let .relative distance := variant.discriminant then
      unless distance < 2^32 do throw "raw relative discriminant exceeds u32"
  let mut previous : Option (Nat × Nat) := none
  let mut seenFields : Array DefinitionIdentity := #[]
  for safety in material.fields do
    unless !seenFields.contains safety.definition do throw "duplicate raw field definition identity"
    seenFields := seenFields.push safety.definition
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

/-- Join the raw declaration with the independently retained source field trees. -/
def Material.validate (material : Material) (template : DefinitionTemplate) : Except String Unit := do
  material.validateRaw
  unless material.fields.size == template.fields.size do
    throw "ADT source field safety and expression domains differ"
  for (field, expression) in material.fields.zip template.fields do
    unless field.variantIndex == expression.variantIndex && field.fieldIndex == expression.fieldIndex do
      throw "ADT source field safety identity differs from field expression"

end AdtDeclaration
end Miri.Input
