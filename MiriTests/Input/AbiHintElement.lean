import Miri.Input.CallCompatibility

open Lean Miri Miri.Input

private def registerJson (hint : Json) : Json :=
  Json.mkObj [("kind", Json.mkObj [("kind", .str "vector"), ("hint_element", hint)]),
    ("size_bits", toJson (128 : Nat))]

private def check (hint : Json) (expected : ABI.Primitive) : IO Unit := do
  let .ok source := DecoderValues.parseAbiRegister (registerJson hint) "register"
    | throw (IO.userError "register decoding failed")
  let .ok result := CallCompatibility.register source
    | throw (IO.userError "register conversion failed")
  unless decide (result.kind = .Vector (hintVectorElem := expected)) do
    throw (IO.userError "register hint changed")

def main : IO Unit := do
  check (Json.mkObj [("kind", .str "integer"), ("integer_kind", .str "i32"),
    ("signed", .bool true)]) (.Int .I32 true)
  check (Json.mkObj [("kind", .str "float"), ("float_kind", .str "f16b")]) (.Float .F16B)
  check (Json.mkObj [("kind", .str "pointer"), ("address_space", toJson (3 : Nat))]) (.Pointer ⟨3⟩)
  let .ok overflowing := DecoderValues.parseAbiRegister (registerJson (Json.mkObj [
      ("kind", .str "pointer"), ("address_space", toJson (2^32 : Nat))])) "overflow"
    | throw (IO.userError "pointer hint decoding failed")
  match CallCompatibility.register overflowing with
  | .error (.invalid ..) => pure ()
  | _ => throw (IO.userError "overflowing address space was not invalid")
  let malformed := registerJson (Json.mkObj [("kind", .str "integer"),
    ("integer_kind", .str "i32"), ("signed", .str "true")])
  match DecoderValues.parseAbiRegister malformed "malformed" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed signedness accepted")
  IO.println "semantic ABI hints: PASS"
