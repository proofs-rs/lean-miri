import MiriTests.Input.JsonFixtures
import Miri.Input.Decoder

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def obj (fields : Array (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.toList.map fun (key, value) =>
    Json.renderString key ++ ":" ++ value) ++ "}"
private def arr (values : Array String) : String :=
  "[" ++ String.intercalate "," values.toList ++ "]"
private def fields (source : String) : Except String (Array (String × String)) := do
  return (← (← JsonFixtures.parse source).object).map fun (key, value) => (key, value.text)
private def get (source key : String) : Except String String := do
  return (← (← JsonFixtures.parse source).field key).text
private def items (source : String) : Except String (Array String) := do
  return (← (← JsonFixtures.parse source).array).map (·.text)
private def set (source key value : String) : Except String String := do
  return obj (#[(key,value)] ++ (← fields source).filter (fun item => item.1 != key))

/-- Permute every object, including tagged payloads, without changing array IDs. -/
private partial def permuted (value : Json) : String :=
  match value with
  | .obj values => obj (values.toArray.reverse.map fun (key, child) => (key, permuted child))
  | .arr values => arr (values.map permuted)
  | value => value.compress

private def replaceBody (source : String) (change : String → Except String String) : Except String String := do
  let bodies ← items (← get source "bodies")
  let some body := bodies[0]? | throw "missing fixture body"
  set source "bodies" (arr (bodies.set! 0 (← change body)))

private def reject (source label : String) : IO Unit :=
  check (!(decodeJson source).isOk) s!"accepted invalid {label}"

private def constant (bits : String) : String :=
  "{\"constant\":{\"value\":{\"bits_unsigned\":" ++ Json.renderString bits ++
  ",\"kind\":\"scalar\"}," ++
  "\"kind\":\"evaluated_const\"},\"user_type_annotation\":null,\"span\":0,\"type\":1}"

private def forwardOrder (source : String) : Except String String := do
  let fs ← fields source
  let body ← get source "bodies"
  let layouts ← get source "layouts"
  return obj (#[("bodies",body)] ++
    fs.filter (fun item => item.1 != "bodies" && item.1 != "layouts") ++ #[("layouts",layouts)])

private def checkCallEvidence : IO Unit := do
  let parse (kind inst slot : String) := JsonReader.run DecodeMIR.callEvidence (obj #[
    ("dispatch_slot", slot), ("fn_abi", "0"), ("function_type", "0"),
    ("instance_id", inst), ("kind", Json.renderString kind)])
  let direct ← must (parse "resolved_instance" "3" "null")
  check (direct.kind == .direct && direct.instanceId == some 3 && direct.dispatchSlot == none)
    "direct-call nullable dispatch slot changed resolution"
  let indirect ← must (parse "indirect_function_pointer" "null" "null")
  check (indirect.kind == .indirect && indirect.instanceId == none && indirect.dispatchSlot == none)
    "indirect-call nullable instance changed resolution"
  let virtualCall ← must (parse "virtual_dispatch" "3" "4")
  check (virtualCall.kind == .virtualDispatch && virtualCall.instanceId == some 3 &&
    virtualCall.dispatchSlot == some 4) "virtual-call required resolution changed"
  check (!(parse "virtual_dispatch" "null" "4").isOk)
    "virtual call accepted a null required instance"
  check (!(parse "virtual_dispatch" "3" "null").isOk)
    "virtual call accepted a null required dispatch slot"

def main : IO Unit := do
  checkCallEvidence
  let fixture ← IO.FS.readFile "tests/input/fixtures/strict-unit.json"
  let baseline ← must (decodeJson fixture)
  let withConstant ← must (replaceBody fixture fun body => set body "required_consts" (arr #[constant "255"]))
  let expected ← must (decodeJson withConstant)
  let reordered ← must (forwardOrder (permuted (← must (Json.parse withConstant))))
  let decoded ← must (decodeJson reordered)
  check (decoded.document.types.size == baseline.document.types.size) "field permutation changed type table"
  check (decoded.document.bodies.map (·.mir) == expected.document.bodies.map (·.mir))
    "recursive field permutation changed final MIR"
  let some body := decoded.document.bodies[0]? | throw (IO.userError "missing decoded body")
  let cs := body.requiredConsts
  let some c := cs[0]? | throw (IO.userError "missing required constant")
  match c.value with
  | .Val (.Scalar (.Int bits width)) ty =>
    check (bits == 255 && width == 1 && ty == 1) "forward layout did not resolve scalar width"
  | _ => throw (IO.userError "wrong resolved scalar constant")
  let asmRegister := "{\"name\":\"reg\",\"arch\":\"X86_64\",\"kind\":\"register_class\"}"
  let asmInput := obj #[("value", obj #[("constant", constant "255"), ("kind", "\"Constant\"")]),
    ("register", asmRegister), ("kind", "\"in\"")]
  let parsedAsm ← must (JsonReader.run DecodeMIR.asmOperand asmInput)
  match parsedAsm with
  | .In _ (.Constant c) => check (c.typeId == 1 && c.span.id == 0) "inline assembly input constant metadata changed"
  | _ => throw (IO.userError "inline assembly input constant was not decoded")
  for kind in #["const", "sym_fn"] do
    let _ ← must (JsonReader.run DecodeMIR.asmOperand (obj #[("value", constant "255"),
      ("kind", Json.renderString kind)]))
    pure ()
  reject (← must (replaceBody fixture fun body => set body "required_consts" (arr #[constant "256"]))) "scalar overflow"
  reject (← must (replaceBody fixture fun body => set body "required_consts" (arr #[constant "-1"]))) "negative scalar"
  reject (← must (set fixture "schema_version" "-1")) "negative table integer"
  reject (← must (replaceBody fixture fun body => set body "def_id" "999999")) "dangling definition"
  reject (← must (replaceBody fixture fun body => set body "locals"
    "[{\"local\":0,\"type\":-1,\"source_info\":{\"scope\":0,\"span\":0}}]")) "negative reference"
  reject (← must (replaceBody fixture fun body => set body "locals"
    "[{\"local\":0,\"local\":0,\"type\":0,\"source_info\":{\"scope\":0,\"span\":0}}]")) "nested duplicate"
  let fs ← must (fields fixture)
  reject (obj (#[("schema", "\"lean-miri-rustc-mir\"")] ++ fs)) "root duplicate"
  let unknown ← must (set reordered "future_metadata" "{\"rows\":[null,true,-2.5e3,{\"escaped\":\"\\uD83D\\uDE03\"}]}")
  let _ ← must (decodeJson unknown)
  reject (← must (set fixture "future_metadata" "{\"x\":1,\"x\":2}")) "duplicate unknown member"
  reject (← must (set fixture "future_metadata" "{\"rows\":[1,]}")) "malformed unknown payload"
  reject (← must (replaceBody fixture fun body => set body "phase" "{\"kind\":\"built\",\"phase\":null}")) "invalid union payload"
  IO.println "TwoPassDecoder: arbitrary object order, forward scalar widths, duplicate keys and malformed references checked"
