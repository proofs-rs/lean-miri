import Miri.Input.CompilerSourceSymbols

/-! Pinned rustc_symbol_mangling::symbol_name_from_attrs. Current-World Item
identity selects only declaration inputs; generic mangling and codegen shim
attribute adjustments remain unavailable. No DefPath substitutes for a symbol. -/
namespace Miri.Input.SourceCompilerSymbolNames
open Miri.Interpreter

/-- Fixed source attribute names are independent of concrete substitutions.
The wasm import exception occurs after std-internal symbol handling; the latter
still uses the shared exact supported v0 identifier rule. -/
def fromDeclaration (material : SourceSymbolNames.Material)
    (declaration : SourceSymbolNames.Declaration) : Except String String := do
  if !declaration.attributes.stdInternalSymbol && declaration.foreignItem &&
      material.isLikeWasm && declaration.wasmImportModule.isSome then
    throw "Unsupported source wasm import symbol mangling"
  CompilerSourceSymbols.symbolFromAttributes material.internalSymbolNamespace declaration.attributes

def symbolName (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String String := do
  let node ← SourceCompilerWorld.node world callee
  let definition ← match node.instanceKind with
    | .Item definition | .LlvmIntrinsic definition => pure definition
    | _ => throw "Unsupported source codegen shim symbol attribute adjustments"
  let some raw := world.canonical.definitions[definition]? | throw "symbol naming canonical definition absent"
  let some source := world.canonical.sourceMaterial | throw "symbol naming typed source absent"
  let some abi := source.abi | throw "symbol naming ABI source absent"
  let some material := abi.symbolNames | throw "symbol naming declaration attributes unavailable"
  let [declaration] := (material.declarations.filter (·.definition == raw)).toList
    | throw "symbol naming declaration attributes absent/ambiguous"
  fromDeclaration material declaration
end Miri.Input.SourceCompilerSymbolNames
