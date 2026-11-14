import Lean.Data.Json.FromToJson
import Miri.Input.TraitSelection.Codec

/-! Strict source-catalog component tests. Unretained source RHS material is
explicitly unavailable; it is never reconstructed from a query answer. -/
open Lean Miri.Input Miri.Input.TraitSelection Miri.Input.GenericSubstitution

private def object := Json.mkObj
private def identity (n : Nat) := object [("crate", toJson (0 : Nat)), ("index", toJson n)]
private def associated (retained : Option Bool) : Json := object <|
  [("trait_associated_definition", identity 3), ("implementation_definition", identity 4),
   ("has_value", .bool true), ("requires_hidden_type_inference", .bool false)] ++
  (retained.toList.map fun value => ("material_retained", .bool value))
private def catalog (retained : Option Bool) : Json :=
  let implementation := object [
    ("definition", identity 2), ("parameters", toJson (#[] : Array Json)),
    ("trait_ref", object [("definition", identity 1), ("arguments", toJson #[object [
      ("kind", .str "atom"), ("sort", .str "type"), ("tag", .str "uint"), ("payload", .str "u8")]])]),
    ("polarity", .str "positive"), ("is_default", .bool false),
    ("associated_values", toJson #[associated retained]),
    ("methods", toJson (#[] : Array Json)), ("constants", toJson (#[] : Array Json))]
  let declaration := object [
    ("definition", identity 1), ("parameters", toJson #[Json.str "type"]),
    ("is_alias", .bool false), ("is_auto", .bool false), ("is_unsafe", .bool false),
    ("is_coinductive", .bool false), ("is_marker", .bool false), ("lang_item", .null),
    ("super_predicates", toJson (#[] : Array Json)), ("members", toJson (#[] : Array Json)),
    ("implementations", toJson #[implementation])]
  object [("traits", toJson #[declaration]), ("constructor_scope", object [("kind", .str "all_source_impls")])]

def main : IO Unit := do
  let unavailable : DefinitionIdentity → Except String (Option DefinitionTemplate) := fun _ =>
    .error "template resolver must not be called for an unretained RHS"
  match Codec.readProgram unavailable (catalog (some false)) with
  | .error error => throw (IO.userError error)
  | .ok program =>
    let some value := program.traits[0]?.bind (·.implementations[0]?) | throw (IO.userError "missing impl")
    let some rhs := value.associatedValues[0]? | throw (IO.userError "missing associated declaration")
    unless rhs.hasValue && !rhs.materialRetained && rhs.expression.isNone do
      throw (IO.userError "source availability marker was lost")
  for raw in #[catalog none, catalog (some true)] do
    match Codec.readProgram unavailable raw with
    | .ok _ => throw (IO.userError "missing required material was accepted")
    | .error _ => pure ()
  let emptyTraits := toJson (#[] : Array Json)
  let duplicateScope := object [("kind", .str "closed_source_constructors"),
    ("constructors", toJson #[identity 5, identity 5])]
  for raw in #[object [("traits", emptyTraits)],
      object [("traits", emptyTraits), ("constructor_scope", duplicateScope)]] do
    match Codec.readProgram unavailable raw with
    | .ok _ => throw (IO.userError "incomplete/ambiguous constructor scope was accepted")
    | .error _ => pure ()
  IO.println "trait source codec: explicit unretained RHS and strict missing-material controls PASS"
