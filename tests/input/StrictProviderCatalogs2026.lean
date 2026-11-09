import Miri.Input.CompilerShimAbi
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerNamedGlobals

open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)
private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (·.1 != key)))
private def reject (value : Except String α) (label : String) : IO Unit :=
  if value.isOk then throw (IO.userError s!"{label}: invalid catalog accepted") else pure ()

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected successful root with no shim catalogs")
  let source ← IO.FS.readFile path
  let decoded ← must (decodeJson source)
  let program ← must (lowerProgram decoded.document)
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let shim ← must (CompilerShimAbi.prepare runtime)
  let named ← must (CompilerNamedShimAbi.prepare runtime)
  let constants ← must (CompilerNamedConstants.prepare runtime program)
  let globals ← must (CompilerNamedGlobals.prepare runtime program)
  unless shim.entries.isEmpty && named.entries.isEmpty && constants.entries.isEmpty && globals.entries.isEmpty do
    throw (IO.userError "unrequested catalogs fabricated entries")
  reject (CompilerShimAbi.expectedAbi shim ⟨.C, #[], .unit⟩) "missing exact shim query"
  reject (CompilerNamedShimAbi.expectedAbi named "getrandom") "missing exact named query"
  reject (CompilerNamedConstants.value constants "ENOENT") "missing exact constant query"
  for field in #["compiler_shim_abis", "compiler_named_shim_abis", "compiler_named_constants", "compiler_named_statics"] do
    let raw ← must (set (← must (Json.parse source)) field (.str "invalid array"))
    reject (decodeJson raw.compress) field
  IO.println "StrictProviderCatalogs2026: absent catalogs stay empty; requests and malformed catalogs fail"
