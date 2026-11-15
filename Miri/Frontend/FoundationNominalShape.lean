import Miri.Frontend.FoundationPhysicalTypes

namespace Miri.Frontend.Foundation
open Lean
/-- Assemble an ADT shape only from validated declaration rows and already
interned substituted field/argument identities. No physical layout is inferred
from names or definition paths. -/
def nominalTypeNode (d : Document) (definition id layoutId : Nat)
    (arguments : Array Nat) (fieldIds : Array (Array Nat)) : Except String Input.TypeNode := do
  let some defn := d.definitions[definition]? | throw "nominal declaration absent"
  let adt ← defn.getObjVal? "adt"
  let kind ← match ← adt.getObjValAs? String "kind" with
    | "struct" => pure Input.AdtKind.structKind
    | "enum" => pure Input.AdtKind.enumKind
    | _ => throw "unsupported nominal shape kind"
  let repr ← adt.getObjVal? "representation"
  -- The physical query has already checked this representation subset.
  for key in #["align_bytes", "integer", "pack_bytes", "scalable_element"] do
    unless (← repr.getObjVal? key) == Json.null do throw "unsupported nominal shape repr"
  let flags ← repr.getObjValAs? Nat "flags_bits"
  unless #[0,4,8].contains flags do throw "unsupported nominal shape flags"
  let representation : Input.ReprOptions := ⟨none, none, none, flags, none,
    ← repr.getObjValAs? Nat "field_shuffle_seed"⟩
  let sourceVariants ← adt.getObjValAs? (Array Json) "variants"
  unless sourceVariants.size == fieldIds.size do throw "nominal variant identity count"
  let mut variants := #[]
  for i in [:sourceVariants.size] do
    let some v := sourceVariants[i]? | throw "nominal variant absent"
    let some ids := fieldIds[i]? | throw "nominal variant identities absent"
    let sourceFields ← v.getObjValAs? (Array Json) "fields"
    unless ids.size == sourceFields.size do throw "nominal field identity count"
    let mut fields := #[]
    for j in [:sourceFields.size] do
      let some f := sourceFields[j]? | throw "nominal field absent"
      let some typeId := ids[j]? | throw "nominal field identity absent"
      fields := fields.push ⟨j, ← f.getObjValAs? String "name", typeId⟩
    variants := variants.push ⟨i, ← v.getObjValAs? String "name", fields⟩
  let shape : Input.TypeShape := .adt ⟨definition, kind, representation,
    arguments.map MIR.GenericArg.Type, variants⟩
  return { id, layoutId, shape, display := ← defn.getObjValAs? String "path" }
end Miri.Frontend.Foundation
