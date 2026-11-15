import Miri.Frontend.FoundationSourceSymbolNames
import Miri.Input.SourceCompilerSymbolNames
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unsupported symbol spelling accepted") | .error _ => pure ()
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine symbol-attribute source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let some material ← checked (SourceSymbolNamesParser.material document)
    | throw (IO.userError "naming source capability absent")
  for (item,expected) in #[
      ("renamed","exact_export"),("plain","plain"),
      ("renamed_import","exact_import"),("default_import","default_import")] do
    let [declaration] := (material.declarations.filter (·.attributes.itemName == some item)).toList
      | throw (IO.userError s!"genuine naming declaration {item} absent/ambiguous")
    unless (← checked (Input.SourceCompilerSymbolNames.fromDeclaration material declaration)) == expected do
      throw (IO.userError s!"fixed symbol spelling differs for {item}")
    if declaration.foreignItem then
      let imported := {declaration with wasmImportModule := some "source_module"}
      rejects (Input.SourceCompilerSymbolNames.fromDeclaration {material with isLikeWasm := true} imported)
      unless (← checked (Input.SourceCompilerSymbolNames.fromDeclaration {material with isLikeWasm := false} imported)) == expected do
        throw (IO.userError "native naming incorrectly applied wasm import exception")
    rejects (Input.SourceCompilerSymbolNames.fromDeclaration material
      {declaration with attributes := {declaration.attributes with procMacroDeclarations := true}})
  let [ordinary] := (material.declarations.filter (·.attributes.itemName == some "needs_mangling")).toList
    | throw (IO.userError "genuine ordinary mangling control absent")
  rejects (Input.SourceCompilerSymbolNames.fromDeclaration material ordinary)
  let some first := material.declarations[0]? | throw (IO.userError "naming declarations absent")
  rejects ({material with declarations := material.declarations.push first}.validate)
  IO.println "genuine fixed/export/import names pass; generic mangling, wasm-import and proc-macro unavailable cases reject"
