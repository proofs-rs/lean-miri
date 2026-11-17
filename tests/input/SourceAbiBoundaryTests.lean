import Miri.Input.Decoder
import Miri.Input.SourceAbiRuntime

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error reason => throw (IO.userError reason)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def setField (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  return Json.mkObj ((key,child) :: fields.toList.filter (·.1 != key))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected source-material MIR input")
  let text ← IO.FS.readFile path
  let decoded ← must (decodeJson text)
  let document := decoded.document
  let some material := document.sourceAbi | throw (IO.userError "missing source ABI material")
  let raw ← must (Json.parse text)
  let source ← must (raw.getObjVal? "source_abi")
  let definitions ← must ((source.getObjVal? "definitions").bind Json.getArr?)
  let some selected := material.definitions.findSome? id
    | throw (IO.userError "control requires a concrete callable instance")
  let some row := definitions[selected.instanceId]? | throw (IO.userError "missing raw source signature")
  let reject (source : Json) (message : String) : IO Unit := do
    let modified ← must (setField raw "source_abi" source)
    check (!(decodeJson modified.compress).isOk) message
  let fields ← must raw.getObj?
  let missing := Json.mkObj (fields.toList.filter (·.1 != "source_abi"))
  check (!(decodeJson missing.compress).isOk) "missing source ABI material accepted"
  reject (← must (setField source "definitions" (.arr (definitions.push row))))
    "duplicate source instance signature accepted"
  let wrongIdentity ← must (setField row "instance_id" (toJson document.instances.size))
  reject (← must (setField source "definitions" (.arr (definitions.set! selected.instanceId wrongIdentity))))
    "out-of-bounds source instance accepted"
  let signature ← must (row.getObjVal? "signature")
  let wrongReturn ← must (setField signature "output" (toJson document.types.size))
  let wrongReturn ← must (setField row "signature" wrongReturn)
  reject (← must (setField source "definitions" (.arr (definitions.set! selected.instanceId wrongReturn))))
    "dangling source signature type accepted"
  let policy ← must (source.getObjVal? "policy")
  let invalidAlignment ← must (setField policy "max_reliable_alignment" (toJson (3 : Nat)))
  reject (← must (setField source "policy" invalidAlignment)) "non-power-of-two ABI alignment accepted"
  let runtime ← must (RuntimeMetadata.ofDocument document |>.mapError toString)
  let _ ← must (SourceAbiRuntime.ofInstance runtime selected.instanceId #[])
  let layout ← must (runtime.lookup selected.signature.output |>.mapError toString)
  let layout := {layout with layout := {layout.layout with size := Miri.ABI.Size.ofBytes 32, backendRepr := .Memory (sized := true)}}
  let queries := {SourceAbiRuntime.queries runtime material.policy with lookup := fun _ => pure layout}
  let signature := {selected.signature with inputs := #[layout.ty], output := layout.ty, abi := .Rust}
  let definition := {selected with signature, virtualCall := false, callerLocation := none}
  for optimize in #[false, true] do
    let abi ← must (SourceAbi.compute {material.policy with optimize} runtime.target queries signature #[] (some definition) true)
    for argument in abi.args.push abi.ret do
      let .Indirect attrs _ _ := argument.mode | throw (IO.userError "large aggregate did not use indirect ABI")
      check (attrs.regular == 670) "Miri ABI acquired codegen body-deduced attributes"
  let incomplete := {material with definitions := material.definitions.set! selected.instanceId none}
  let incompleteRuntime ← must (RuntimeMetadata.ofDocument
    {document with sourceAbi := some incomplete} |>.mapError toString)
  check (!(SourceAbiRuntime.ofInstance incompleteRuntime selected.instanceId #[]).isOk)
    "missing concrete ABI source silently fell back to an answer table"
  IO.println "source ABI boundary: required material, dense identities, type references, policy and no-body-deduced attributes checked; missing source fails at demand"
