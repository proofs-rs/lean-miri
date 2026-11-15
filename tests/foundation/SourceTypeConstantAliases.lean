import Miri.Frontend.FoundationSourceConstValues
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := match value with
  | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit := match value with
  | .error _ => pure () | .ok _ => throw (IO.userError "unproved const alias accepted")
private def replace (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => Json.mkObj ((fields.toList.filter (·.1 != key)) ++ [(key,value)])
  | other => other
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine type-constant-alias source")
  let json ← checked (Json.parse (← IO.FS.readFile path))
  let source ← checked (SourceTypesParser.material json)
  let [alias] := source.constantAliases.toList | throw (IO.userError "expected one original const alias")
  unless alias.kind == .Anon && !alias.rigid && alias.arguments.isEmpty do
    throw (IO.userError "anonymous alias identity/arguments lost")
  let some raw := source.definitions[alias.definition]? | throw (IO.userError "alias definition absent")
  let some values ← checked (SourceConstValuesParser.material json source 64)
    | throw (IO.userError "compiler constant observations absent")
  let [value] := values.rows.toList | throw (IO.userError "expected one observed type const")
  unless value.definition == raw.raw && value.arguments.isEmpty && value.promoted.isNone &&
      value.value == .scalar 4 8 do throw (IO.userError "compiler size_of::<u32> result/key mismatch")
  let some array := source.types.findIdx? (fun type => match type with | .array _ (.alias 0) => true | _ => false)
    | throw (IO.userError "type-level alias token missing")
  rejects (Input.SourceTypes.instantiate source #[] #[] array)
  let resolved ← checked (SourceConstValuesParser.attachAliasValues source (some values))
  let concrete ← checked (Input.SourceTypes.instantiate resolved #[] #[] array)
  let .array (.primitive "uint" "u8") 4 := concrete | throw (IO.userError "witness array length not consumed")
  rejects (SourceConstValuesParser.attachAliasValues source (some {rows := values.rows ++ values.rows}))
  let mismatched := {value with typeRef := (alias.typeRef + 1) % source.types.size}
  unless mismatched.typeRef != alias.typeRef do throw (IO.userError "type mismatch control did not differ")
  rejects (SourceConstValuesParser.attachAliasValues source (some {rows := #[mismatched]}))
  unless source.types.any (fun type => match type with | .array _ (.parameter 0 _) => true | _ => false) do
    throw (IO.userError "symbolic array length was evaluated")
  rejects ({source with types := source.types.push (.array 0 (.alias source.constantAliases.size))}.validate)
  let rows ← checked (json.getObjValAs? (Array Json) "constant_aliases")
  let [row] := rows.toList | throw (IO.userError "source alias row absent")
  rejects (SourceTypesParser.material (replace json "constant_aliases" (toJson #[replace row "definition" (toJson source.definitions.size)])))
  rejects (SourceTypesParser.material (replace json "constant_aliases" (toJson #[replace row "kind" (toJson "unknown")])))
  IO.println "type const alias syntax, observed compiler scalar and malformed controls PASS"
