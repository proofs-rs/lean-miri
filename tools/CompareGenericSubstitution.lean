import Miri.Input.GenericMaterialCodec
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Miri.Input.GenericSubstitution

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: CompareGenericSubstitution ORACLE.json")
  let text ← IO.FS.readFile path
  let result : Except String Nat := do
    let rows ← (← Json.parse text).getArr?
    unless rows.size ≥ 10 do throw "generic material comparison needs at least ten real rustc cases"
    let mut count := 0
    for row in rows do
      let template ← Miri.Input.GenericMaterialCodec.readTerm 256 (← row.getObjVal? "template")
      let source ← Miri.Input.GenericMaterialCodec.readTemplate (← row.getObjVal? "source_material")
      unless source.typeExpression == template do throw "imported declaration template differs from rustc source template"
      let arguments ← (← (← row.getObjVal? "arguments").getArr?).mapM (Miri.Input.GenericMaterialCodec.readTerm 256)
      let expected ← Miri.Input.GenericMaterialCodec.readTerm 256 (← row.getObjVal? "expected")
      let actual ← source.instantiateType 256 arguments
      unless actual == expected do
        throw s!"rustc generic substitution mismatch: Lean={repr actual}; rustc={repr expected}"
      count := count + 1
      let signature ← row.getObjVal? "signature_expected"
      if signature != .null then
        let expected ← Miri.Input.GenericMaterialCodec.readTerm 256 signature
        let actual ← source.instantiateSignature 256 arguments
        unless actual == expected do throw "rustc declaration signature instantiation mismatch"
        count := count + 1
      for field in (← (← row.getObjVal? "field_expected").getArr?) do
        let variantIndex ← (← field.getObjVal? "variant").getNat?
        let fieldIndex ← (← field.getObjVal? "field").getNat?
        let expected ← Miri.Input.GenericMaterialCodec.readTerm 256 (← field.getObjVal? "expected")
        let actual ← source.instantiateField 256 arguments variantIndex fieldIndex
        unless actual == expected do throw "rustc declaration field instantiation mismatch"
        count := count + 1
    pure count
  match result with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"{count} fresh rustc/Lean early substitution comparisons passed"
  pure 0
