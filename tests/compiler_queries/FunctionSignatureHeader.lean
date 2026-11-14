import Miri.Input.Decoder
import Miri.Input.RawFunctionSignature
import Miri.Input.GenericInstantiationWorld

open Lean Miri.Input Miri.Input.GenericSubstitution Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def unit : GenericSubstitution.Term := .node .type "tuple" "" .nil
private def raw (count : Nat) (splatted : Option Nat) : GenericSubstitution.Term :=
  .binder #[] (.node .aggregate "signature" (Json.mkObj [
    ("abi_packed",toJson (2 : Nat)),("safe",toJson true),
    ("c_variadic",toJson false),("splatted",toJson splatted)]).compress
      (Terms.ofArray ((Array.replicate count unit).push unit)))
private def material (count : Nat) (splatted : Option Nat) : Json := Json.mkObj [
  ("inputs",toJson (Array.replicate count (0 : Nat))),("output",toJson (0 : Nat)),
  ("safety",Json.mkObj [("kind",toJson "safe")]),
  ("abi",Json.mkObj [("kind",toJson "rust"),("unwind",Json.null)]),
  ("c_variadic",toJson false),("splatted",toJson splatted)]

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned FnSigKind boundary oracle")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile path))).getArr?)
  unless rows.size == 8 do throw (IO.userError "incomplete FnSigKind boundary oracle")
  let world ← must (World.ofMaterial #[] #[] #[] #[] 8)
  let (unitId,world) ← must ((World.internType (.tuple #[])).run world)
  for row in rows do
    let count ← must ((← must (row.getObjVal? "inputs")).getNat?)
    let splattedValue ← must (row.getObjVal? "splatted")
    let splatted ← if splattedValue == .null then pure none else some <$> must splattedValue.getNat?
    let accepted ← must ((← must (row.getObjVal? "accepted")).getBool?)
    unless (RawFunctionSignature.read (raw count splatted)).isOk == accepted do
      throw (IO.userError "raw source header differs from FnSigKind")
    unless (JsonReader.run (DecoderValues.parseFunctionSignature "header-oracle")
        (material count splatted).compress).isOk == accepted do
      throw (IO.userError "material function header differs from FnSigKind")
    let constructor := Constructor.functionPointer {
      abiPacked := 2, safe := true, cVariadic := false, splatted,
      inputs := Array.replicate count unitId, output := unitId}
    unless ((World.internType constructor).run world).isOk == accepted do
      throw (IO.userError "direct World constructor differs from FnSigKind")
    let term := GenericSubstitution.Term.node .type "function_pointer" "" (.cons (raw count splatted) .nil)
    unless ((GenericInstantiationWorld.resolveType 4096 term).run world).isOk == accepted do
      throw (IO.userError "generic function constructor differs from FnSigKind")
  unless !(RawFunctionSignature.validateSplatted 1000 (some 256)).isOk do
    throw (IO.userError "non-u8 splatted index was accepted")
  IO.println "PASS 8 actual FnSigKind boundaries across raw/material/generic/direct World headers"
