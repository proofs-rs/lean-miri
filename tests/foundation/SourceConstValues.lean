import Miri.Frontend.FoundationSourceMaterial
/-! Run against a snapshot export of fixtures/constant-entry.rs (main/start/unused),
optionally followed by an ordinary same-compiler export of constant-value.rs
(root probe) as the independent
value oracle. The snapshot contains compiler CTFE outputs, not Lean CTFE. -/
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := match value with
  | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit := match value with
  | .error _ => pure () | .ok _ => throw (IO.userError "malformed concrete constant witness accepted")
private def replace (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => Json.mkObj ((fields.toList.filter (·.1 != key)) ++ [(key,value)])
  | other => other
def main (paths : List String) : IO Unit := do
  let path :: rest := paths | throw (IO.userError "expected genuine concrete constant source")
  let json ← checked (Json.parse (← IO.FS.readFile path))
  let source ← checked (SourceTypesParser.material json)
  let result ← checked (SourceConstValuesParser.material json source 64)
  let some material := result | throw (IO.userError "concrete constant material missing")
  let [row] := material.rows.toList | throw (IO.userError "expected exactly one observed concrete key")
  unless row.value == .scalar 8 8 do throw (IO.userError "compiler SIZE<u64> value mismatch")
  unless row.arguments.size == 1 && row.promoted == none do throw (IO.userError "concrete key lost full arguments")
  let [.type arg] := row.arguments.toList | throw (IO.userError "type argument missing")
  unless source.types[arg]? == some (.primitive "uint" "u64") do throw (IO.userError "concrete u64 key mismatch")
  let encoded ← checked (json.getObjVal? "evaluated_const_values")
  let [original] := (← checked (encoded.getObjValAs? (Array Json) "rows")).toList
    | throw (IO.userError "genuine row missing")
  let badRows (rows : Array Json) := replace json "evaluated_const_values" (Json.mkObj [("rows",toJson rows)])
  let parse := fun changed => SourceConstValuesParser.material changed source 64
  rejects (parse (badRows #[original,original]))
  rejects (parse (badRows #[replace original "arguments" (toJson (#[] : Array Json))]))
  let value ← checked (original.getObjVal? "value")
  rejects (parse (badRows #[replace original "value" (replace value "size_bytes" (toJson (4:Nat)))]))
  rejects (parse (badRows #[replace original "value" (replace value "bits" (toJson "18446744073709551616"))]))
  rejects (parse (badRows #[replace original "arguments" (toJson #[Json.mkObj [("kind",toJson "lifetime"),("region",toJson "unbound")]])]))
  let unboundSource := {source with types := source.types.push (.parameter 0 "T")}
  let unbound := replace original "arguments" (toJson #[Json.mkObj [("kind",toJson "type"),("type",toJson source.types.size)]])
  rejects (SourceConstValuesParser.material (badRows #[unbound]) unboundSource 64)
  let scalarSource := {source with types := source.types.push (.primitive "bool" "bool") |>.push (.primitive "char" "char")}
  let scalarKey (typeRef bits bytes : Nat) :=
    replace (replace original "parameters" (toJson #["const"])) "arguments" (toJson #[Json.mkObj [
      ("kind",toJson "const"),("value",Json.mkObj [("kind",toJson "value"),
        ("type",toJson typeRef),("bits",toJson (toString bits)),("size_bytes",toJson bytes)])]])
  -- These malformed keys have valid widths and parameter kinds. Their invalid
  -- scalar values must be rejected by ground-key validation, not another check.
  for (typeRef,bits,bytes) in #[(source.types.size,2,1),
      (source.types.size+1,0xd800,4),(source.types.size+1,0x110000,4)] do
    rejects (SourceConstValuesParser.material (badRows #[scalarKey typeRef bits bytes]) scalarSource 64)
  let document ← checked (decode json)
  let carrier ← checked (typedSourceMaterial document)
  unless carrier.constantValues == some material do throw (IO.userError "factory did not retain typed values")
  if let referencePath :: _ := rest then
    let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
    let bodies ← checked (reference.getObjValAs? (Array Json) "bodies")
    let [body] := bodies.toList | throw (IO.userError "expected one compiler oracle body")
    let [constant] := (← checked (body.getObjValAs? (Array Json) "required_consts")).toList
      | throw (IO.userError "expected one compiler evaluated constant")
    let evaluated ← checked ((← checked (constant.getObjVal? "constant")).getObjVal? "value")
    unless (← checked (evaluated.getObjValAs? String "bits_unsigned")) == "8" &&
        (← checked (evaluated.getObjValAs? Nat "size_bytes")) == 8 do
      throw (IO.userError "same-compiler oracle disagrees")
  IO.println "trusted concrete SIZE<u64> row, exact key, factory and malformed controls PASS"
