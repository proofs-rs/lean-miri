import Miri.Input.RawFunctionSignature
import Miri.Input.GenericMaterialCodec
open Lean Miri.Input
private def checked (input : Json) : Except String Nat := do
  let rows ← input.getArr?
  for row in rows do
    let raw ← GenericMaterialCodec.readTerm 16384 (← row.getObjVal? "signature")
    let args ← (← (← row.getObjVal? "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 16384)
    let #[expected] := args | throw "leaf source fixture requires one type argument"
    let signature ← RawFunctionSignature.read raw
    unless signature.variables.isEmpty && signature.inputs == #[expected] &&
        signature.output == expected && signature.abi == .Rust &&
        signature.safety == .Safe && !signature.cVariadic && signature.splatted.isNone do
      throw "raw signature parser differs from actual leaf<T>(T)->T declaration"
  unless rows.size == 2 do throw "raw signature oracle omitted concrete type cases"
  let bad := GenericSubstitution.Term.binder #[] (.node .aggregate "signature"
    "{\"abi_packed\":40,\"safe\":true,\"c_variadic\":false,\"splatted\":null}"
    (.cons (.atom .type "uint" "u32") .nil))
  unless (RawFunctionSignature.read bad).toOption.isNone do
    throw "raw signature accepted invalid packed ABI"
  let missing := GenericSubstitution.Term.binder #[] (.node .aggregate "signature"
    "{\"abi_packed\":2,\"safe\":true,\"c_variadic\":false}"
    (.cons (.atom .type "uint" "u32") .nil))
  unless (RawFunctionSignature.read missing).toOption.isNone do
    throw "raw signature defaulted a missing source header field"
  pure rows.size

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected independent instantiated raw signature oracle")
  match Json.parse (← IO.FS.readFile path) >>= checked with
  | .ok count => IO.println s!"PASS {count} actual raw function signatures; invalid ABI and missing header reject"
  | .error error => throw (IO.userError error)
