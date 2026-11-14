import Miri.Input.BinderRegions
import Miri.Input.GenericMaterialCodec

open Lean Miri.Input Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned raw/normalized oracle")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile path))).getArr?)
  unless rows.size == 9 do throw (IO.userError "incomplete binder oracle")
  for row in rows do
    let source ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let expected ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "normalized")))
    unless (← must (BinderRegions.eraseAndAnonymize 4096 source)) == expected do
      throw (IO.userError "region binder normalization differs from pinned rustc")
    unless (← must (BinderRegions.eraseAndAnonymize 4096 expected)) == expected do
      throw (IO.userError "region binder normalization is not idempotent")
  let malformed := Term.binder #[] (.bound .region (.Bound 0) 0 .anonymous)
  if (BinderRegions.eraseAndAnonymize 512 malformed).isOk then
    throw (IO.userError "missing bound variable was accepted")
  let wrongIdentity := Term.binder #[.region .anonymous]
    (.bound .region (.Bound 0) 0 (.namedForPrinting "'x"))
  if (BinderRegions.eraseAndAnonymize 512 wrongIdentity).isOk then
    throw (IO.userError "inconsistent owned variable identity was accepted")
  let escaped := Term.binder #[.region .anonymous] (.bound .region (.Bound 1) 0 .anonymous)
  if (BinderRegions.eraseAndAnonymize 512 escaped).isOk then
    throw (IO.userError "escaping bound region was erased")
  if (BinderRegions.eraseAndAnonymize 0 malformed).isOk then
    throw (IO.userError "fuel exhaustion was accepted")
  IO.println "PASS 9 exact pinned binder normalizations, idempotence and malformed/escaping/fuel controls"
