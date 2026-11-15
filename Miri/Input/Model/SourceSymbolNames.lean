import Miri.Input.Model.SourceSymbols

/-! Finite declaration/codegen naming inputs. These are independent of concrete
substitution or a symbol-name query result; generic mangling is not supplied. -/
namespace Miri.Input.SourceSymbolNames
structure Declaration where
  definition : DefinitionId
  attributes : SourceSymbols.Attributes
  foreignItem : Bool
  wasmImportModule : Option String
  deriving Repr, DecidableEq
structure Material where
  internalSymbolNamespace : String
  isLikeWasm : Bool
  declarations : Array Declaration
  deriving Repr, DecidableEq

def Material.validate (material : Material) : Except String Unit := do
  let mut seen : Array DefinitionId := #[]
  for declaration in material.declarations do
    unless declaration.definition.crateIndex < 2^32 && declaration.definition.index < 2^32 &&
        !seen.contains declaration.definition do throw "symbol naming declaration raw identity invalid/duplicated"
    seen := seen.push declaration.definition
    if declaration.wasmImportModule.isSome && !declaration.foreignItem then
      throw "wasm import module belongs to a non-foreign declaration"
end Miri.Input.SourceSymbolNames
