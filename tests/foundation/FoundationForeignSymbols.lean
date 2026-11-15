import Miri.Frontend.FoundationForeignSymbols
open Lean Miri.Frontend.Foundation

private def sample (allocator handler : Option String) : Json := Json.mkObj [
  ("foreign_symbol_material", Json.mkObj [
    ("os", toJson "linux"), ("env", toJson "gnu"), ("binary_format", toJson "elf"),
    ("families", toJson (#["unix"] : Array String)),
    ("internal_symbol_namespace", toJson "_RNvCs0_7___rustc"),
    ("allocator_kind", toJson allocator), ("alloc_error_handler_kind", toJson handler)])]

private def checked (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  for (allocator, handler, count) in [
      (none, none, 0), (some "default", some "default", 5),
      (some "default", some "global", 4), (some "global", some "default", 1),
      (some "global", some "global", 0)] do
    let symbols ← checked (foreignSymbols (sample allocator handler))
    unless symbols.allocatorShims.size == count do throw (IO.userError "allocator selection mismatch")
    unless symbols.exportedCandidates.isNone && symbols.selectedExports.isNone do
      throw (IO.userError "missing export selection was invented")
  for input in [sample (some "unknown") none, sample (some "default") none] do
    match foreignSymbols input with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "invalid allocator selection accepted")
  if let [foundationPath, legacyPath] := args then
    let foundation ← checked (Json.parse (← IO.FS.readFile foundationPath))
    let legacy ← checked (Json.parse (← IO.FS.readFile legacyPath))
    let symbols ← checked (foreignSymbols foundation)
    let runtime ← checked (legacy.getObjVal? "compiler_runtime_queries")
    let expected ← checked (runtime.getObjVal? "foreign_symbols")
    let target ← checked (expected.getObjVal? "target")
    unless symbols.os == (← checked (target.getObjValAs? String "os")) &&
        symbols.env == (← checked (target.getObjValAs? String "env")) &&
        symbols.binaryFormat == (← checked (target.getObjValAs? String "binary_format")) &&
        symbols.families == (← checked (target.getObjValAs? (Array String) "families")) &&
        symbols.noAllocShimSymbol == (← checked (expected.getObjValAs? String "no_alloc_shim_symbol")) do
      throw (IO.userError "foreign target/internal symbol mismatch")
    let actual := symbols.allocatorShims.map fun (symbol, target) => Json.mkObj [
      ("symbol", toJson symbol), ("target", match target with
        | .special method => Json.mkObj [("kind",toJson "special"),("method",toJson method)]
        | .redirect symbol => Json.mkObj [("kind",toJson "redirect"),("symbol",toJson symbol)])]
    unless toJson actual == (← checked (expected.getObjVal? "allocator_shims")) do
      throw (IO.userError "allocator shim derivation differs from pinned exporter")
  IO.println "foundation foreign symbol linkage derivation passed"
