import Miri.Frontend.FoundationForeignDeclarations
import Miri.Input.CompilerSourceSymbols

open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported foreign source accepted")

private def mapItems (document : Json) (change : Json → Json) : Except String Json := do
  let graph ← document.getObjVal? "link_section_material"
  let locals ← graph.getObjValAs? (Array Json) "local_items"
  let dependencies ← (← graph.getObjValAs? (Array Json) "executable_dependencies").mapM fun row => do
    let exports ← (← row.getObjValAs? (Array Json) "exports").mapM fun exported => do
      if (← exported.getObjValAs? String "kind") == "non_generic" &&
          !(← exported.getObjValAs? Bool "is_foreign") then
        return exported.setObjVal! "item" (change (← exported.getObjVal? "item"))
      return exported
    return row.setObjVal! "exports" (toJson exports)
  let updated := (graph.setObjVal! "local_items" (toJson (locals.map change))).setObjVal!
    "executable_dependencies" (toJson dependencies)
  return document.setObjVal! "link_section_material" updated

def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath,expectedCount] := paths | throw (IO.userError "expected source/projected schema12/count")
  let source ← checked (Json.parse (← IO.FS.readFile sourcePath))
  let material ← checked (foreignDeclarations source)
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  check ((← checked (reference.getObjValAs? String "schema")) == "lean-miri-rustc-mir" &&
    (← checked (reference.getObjValAs? Nat "schema_version")) == 12 &&
    (← checked (reference.getObjValAs? String "rustc_commit")) == "8144389c895da997dbdecaa635e41d6a50be6ffd") "foreign oracle pin differs"
  let rows ← checked (reference.getObjValAs? (Array Json) "candidates")
  check (material.declarations.size == rows.size && toString rows.size == expectedCount) "foreign candidate completeness/count differs"
  for (declaration,row) in material.declarations.zip rows do
    let symbol ← checked (Input.CompilerSourceSymbols.symbol material.internalSymbolNamespace declaration)
    check ((← checked (row.getObjValAs? Nat "iteration_index")) == declaration.iterationIndex &&
      (← checked (row.getObjValAs? Bool "used")) == declaration.used &&
      (← checked (row.getObjValAs? String "symbol")) == symbol &&
      (← checked (row.getObjValAs? Bool "weak")) == (declaration.attributes.linkage == some "WeakAny") &&
      (← checked (row.getObjValAs? Bool "explicit_symbol"))) "foreign ordering/symbol attributes differ"
    let definition ← checked (row.getObjVal? "definition")
    check ((← checked (definition.getObjValAs? Nat "crate")) == declaration.definition.crateIndex &&
      (← checked (definition.getObjValAs? Nat "index")) == declaration.definition.index &&
      (← checked (row.getObjValAs? Nat "crate_index")) == declaration.crateIndex &&
      (← checked (row.getObjValAs? String "crate_name")) == declaration.crateName &&
      (← checked (row.getObjValAs? Bool "compiler_builtins")) == declaration.compilerBuiltins &&
      (← checked (row.getObjValAs? String "definition_kind")) == declaration.kind) "foreign DefId/traversal provenance differs"
    let span ← checked (row.getObjVal? "span")
    let start ← checked (span.getObjVal? "start")
    let finish ← checked (span.getObjVal? "end")
    check ((← checked (span.getObjValAs? Bool "is_dummy")) == declaration.span.isDummy &&
      (← checked (span.getObjValAs? String "file")) == declaration.span.file &&
      (← checked (span.getObjValAs? Bool "root_context")) == (declaration.span.context == "#0") &&
      (← checked (start.getObjValAs? Nat "line")) == declaration.span.startLine &&
      (← checked (start.getObjValAs? Nat "column")) == declaration.span.startColumn &&
      (← checked (finish.getObjValAs? Nat "line")) == declaration.span.endLine &&
      (← checked (finish.getObjValAs? Nat "column")) == declaration.span.endColumn) "foreign declaration span source differs"
    let key ← checked (Input.CompilerSourceSymbols.monoKey declaration)
    check (key.definition == declaration.definition && key.arguments.size == declaration.parameters.size)
      "foreign mono key lost original slots"
  let graph ← checked (source.getObjVal? "link_section_material")
  rejects (foreignDeclarations (source.setObjVal! "link_section_material" (graph.setObjVal! "executable_dependencies" Json.null)))
  rejects (foreignDeclarations (source.setObjVal! "link_section_material"
    (graph.setObjVal! "executable_dependencies" (toJson (#[] : Array Json)))))
  let missing ← checked (mapItems source fun item => item.setObjVal! "generic_layers" Json.null)
  rejects (foreignDeclarations missing)
  let linkage ← checked (mapItems source fun item => item.setObjVal! "symbol_linkage" (toJson "Unknown"))
  rejects (foreignDeclarations linkage)
  let layers ← checked (mapItems source fun item => item.setObjVal! "generic_layers" (toJson (#[] : Array Json)))
  rejects (foreignDeclarations layers)
  let spans ← checked (mapItems source fun item => item.setObjVal! "source_span_key" Json.null)
  rejects (foreignDeclarations spans)
  let some declaration := material.declarations[0]? | throw (IO.userError "foreign controls need one declaration")
  rejects (Input.CompilerSourceSymbols.symbol material.internalSymbolNamespace
    {declaration with attributes := {declaration.attributes with procMacroDeclarations := true}})
  rejects (Input.CompilerSourceSymbols.symbol material.internalSymbolNamespace
    {declaration with attributes := {declaration.attributes with stdInternalSymbol := true,symbolName := some "é"}})
  rejects (Input.CompilerSourceSymbols.symbol material.internalSymbolNamespace
    {declaration with attributes := {declaration.attributes with stdInternalSymbol := true,symbolName := some "bad-name"}})
  rejects (Input.CompilerSourceSymbols.symbol material.internalSymbolNamespace
    {declaration with attributes := {declaration.attributes with
      stdInternalSymbol := false, noMangle := true, symbolName := none, itemName := none}})
  rejects (Input.CompilerSourceSymbols.monoKey {declaration with parameters := #[.typeParameter]})
  rejects (Input.CompilerSourceSymbols.monoKey {declaration with parameters := #[.constParameter]})
  IO.println s!"foreign source: {material.declarations.size} ordered declarations match pinned compiler; missing/unsupported source fails closed without instances or winners"
