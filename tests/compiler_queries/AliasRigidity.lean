import Miri.Input.TableCore
import Miri.Input.GenericInstantiation

open Miri.Input Miri.Input.GenericSubstitution Miri.Input.GenericInstantiation

private def wire :=
  r#"{"type_id":0,"display":"same","layout":0,"layout_query_input_type":null,"shape":{"kind":"alias","rigid":true,"alias_payload":{"kind":"Projection","def_id":0},"def_id":0,"generic_args":[]}}"#

def main : IO Unit := do
  let checked : Except String Unit := do
    let node ← JsonReader.run (DecoderValues.parseTypeNode "$alias") wire
    let context : Context := {
      types := #[node], definitions := #[{crateIndex := 3, index := 9}],
      constants := #[], pointerBytes := 8 }
    let actual ← ofType context 32 0
    let expected := Term.definition .type "alias_projection_rigid" ⟨3, 9⟩ .nil
    unless actual == expected do throw "source alias rigidity was lost"
    unless (← resolveType context 32 expected) == 0 do throw "canonical alias identity lookup failed"
    match resolveType context 32 (.definition .type "alias_projection_not_rigid" ⟨3, 9⟩ .nil) with
    | .ok _ => throw "different alias rigidity selected the same type"
    | .error _ => pure ()
    match JsonReader.run (DecoderValues.parseTypeNode "$alias") (wire.replace "\"rigid\":true," "") with
    | .ok _ => throw "missing mandatory alias rigidity was accepted"
    | .error _ => pure ()
  match checked with
  | .ok () => IO.println "alias rigidity import/identity and missing-seed rejection passed"
  | .error error => throw (IO.userError error)
