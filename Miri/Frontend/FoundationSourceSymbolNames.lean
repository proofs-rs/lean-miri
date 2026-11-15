import Miri.Frontend.Foundation
import Miri.Input.Model.SourceSymbolNames

/-! Naming attributes are parsed once; no original JSON or evaluated symbol
answer is retained. An absent source component is unavailable, not empty. -/
namespace Miri.Frontend.Foundation.SourceSymbolNamesParser
open Lean

def material (document : Document) : Except String (Option Input.SourceSymbolNames.Material) := do
  let source ← match document.source.getObjVal? "symbol_name_source" with
    | .ok value => pure value
    | .error _ => return none
  if source == Json.null then return none
  let namespacePrefix ← (← document.source.getObjVal? "foreign_symbol_material").getObjValAs? String "internal_symbol_namespace"
  let wasm ← (← document.source.getObjVal? "session").getObjValAs? Bool "is_like_wasm"
  let declarations ← (← source.getObjValAs? (Array Json) "declarations").mapM fun row => do
    let reference ← row.getObjValAs? Nat "definition"
    let some definition := document.definitions[reference]? | throw "symbol naming source definition absent"
    unless (← definition.getObjValAs? Nat "definition_id") == reference do
      throw "symbol naming source definition/index mismatch"
    let attributes ← row.getObjVal? "attributes"
    return ({
      definition := ⟨← definition.getObjValAs? Nat "crate_index",← definition.getObjValAs? Nat "index"⟩
      foreignItem := ← row.getObjValAs? Bool "foreign_item"
      wasmImportModule := ← row.getObjValAs? (Option String) "wasm_import_module"
      attributes := {
        symbolName := ← attributes.getObjValAs? (Option String) "symbol_name"
        itemName := ← attributes.getObjValAs? (Option String) "item_name"
        noMangle := ← attributes.getObjValAs? Bool "no_mangle"
        stdInternalSymbol := ← attributes.getObjValAs? Bool "std_internal_symbol"
        linkage := ← attributes.getObjValAs? (Option String) "linkage"
        procMacroDeclarations := ← attributes.getObjValAs? Bool "proc_macro_declarations" } } : Input.SourceSymbolNames.Declaration)
  let result : Input.SourceSymbolNames.Material := ⟨namespacePrefix,wasm,declarations⟩
  result.validate
  return some result
end Miri.Frontend.Foundation.SourceSymbolNamesParser
