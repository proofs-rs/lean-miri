import Miri.Input.Decoder
import Miri.Input.GenericMaterialCodec
import Miri.Input.GenericInstantiation

/-! Fresh pinned-rustc FnDef trees are an independent oracle. Production GI
reads only declaration/type material, never these expected-result rows. -/
open Lean Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [inputPath,oraclePath] := args | throw (IO.userError "expected fresh input.json oracle.json")
  let document := (← must (decodeJson (← IO.FS.readFile inputPath))).document
  let context ← must (GenericInstantiation.Context.ofDocument document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size ≥ 3 do throw (IO.userError "FnDef oracle requires three actual Rust callees")
  let mut signatureBinders := 0
  for row in rows do
    let expected ← must (GenericMaterialCodec.readTerm 1024 (← must (row.getObjVal? "expected")))
    let argumentCount ← must ((← must (row.getObjVal? "argument_binders")).getNat?)
    let signatureCount ← must ((← must (row.getObjVal? "signature_binders")).getNat?)
    let id ← must (GenericInstantiation.resolveType context 1024 expected)
    let actual ← must (GenericInstantiation.ofType context 1024 id)
    unless actual == expected do throw (IO.userError "FnDef rustc/Lean type tree mismatch")
    let node ← must (context.node id)
    let .functionDefinition _ _ _ signatureVariables argumentVariables := node.shape
      | throw (IO.userError "FnDef resolved to a different source constructor")
    unless argumentVariables.size == argumentCount && signatureVariables.size == signatureCount do
      throw (IO.userError "FnDef argument/signature binder material disagrees with rustc")
    if signatureCount > 0 then signatureBinders := signatureBinders + 1
  unless signatureBinders > 0 do throw (IO.userError "FnDef fixture lacks distinct nonempty signature binder")
  IO.println s!"PASS {rows.size} fresh rustc/Lean FnDef identities; nonempty_signature_binders={signatureBinders}"
