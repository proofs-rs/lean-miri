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
  let decoded ← must (decodeJson (← IO.FS.readFile path))
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
    let raw ← must (set runtime.source.raw field (.str "invalid array"))
    let runtime := { runtime with source := { runtime.source with raw := raw }, nodeCache := none }
    let program := { program with input := { program.input with raw := raw } }
    match field with
    | "compiler_shim_abis" => reject (CompilerShimAbi.prepare runtime) field
    | "compiler_named_shim_abis" => reject (CompilerNamedShimAbi.prepare runtime) field
    | "compiler_named_constants" => reject (CompilerNamedConstants.prepare runtime program) field
    | _ => reject (CompilerNamedGlobals.prepare runtime program) field
  IO.println "StrictProviderCatalogs2026: absent catalogs stay empty; requests and malformed catalogs fail"
