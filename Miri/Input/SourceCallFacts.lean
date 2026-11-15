import Miri.Input.SourceCompilerSymbolNames

/-! machine.rs::find_mir_or_eval_fn asks tcx.is_foreign_item(instance.def_id()).
Pinned rustc_middle/hir/mod.rs defines that property by the definition's immediate
ForeignMod parent. Finite generic declaration attributes retain that source
property; ABI convention and diagnostic names do not decide foreignness. -/
namespace Miri.Input.SourceCallFacts
open Miri.Interpreter

def isForeignItem (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String Bool := do
  let node ← SourceCompilerWorld.node world callee
  let definition := node.instanceKind.defId
  let some raw := world.canonical.definitions[definition]? | throw "foreign-item definition absent"
  let some material := world.canonical.sourceMaterial | throw "foreign-item source material unavailable"
  let some abi := material.abi | throw "foreign-item declaration attributes unavailable"
  let [header] := (abi.functions.filter (·.definition == raw)).toList
    | throw "foreign-item declaration attributes absent/ambiguous"
  return header.attributes.foreignItem

/-- Declaration attributes determine fixed names through the same current
World; unsupported mangling and missing source remain explicit failures. -/
def symbolName (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String String :=
  SourceCompilerSymbolNames.symbolName world callee

/-- Pinned ty/util.rs:594 tests exactly the source DefKind::Closure. -/

def isClosureLike (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String Bool := do
  let node ← SourceCompilerWorld.node world callee
  let some raw := world.canonical.definitions[node.instanceKind.defId]?
    | throw "closure-like canonical definition absent"
  let some source := world.canonical.sourceMaterial | throw "closure-like typed source unavailable"
  let some physical := source.physical | throw "closure-like declaration kinds unavailable"
  let [row] := (physical.definitions.filter (·.raw == raw)).toList
    | throw "closure-like source definition absent/ambiguous"
  match row.kind with
  | "closure" => pure true
  | "fn" | "assoc_fn" => pure false
  | tag => throw s!"Unsupported closure-like source definition kind {tag}"

/-- Miri intrinsics/mod.rs:163 reads the raw CodegenFnAttrs.symbol_name, not
symbol_name(instance). Captured null is distinct from a missing declaration. -/
def codegenSymbolName (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String (Option String) := do
  let node ← SourceCompilerWorld.node world callee
  let .LlvmIntrinsic definition := node.instanceKind
    | throw "LLVM symbol attribute query on non-LLVM source instance"
  let some raw := world.canonical.definitions[definition]? | throw "LLVM source definition absent"
  let some source := world.canonical.sourceMaterial | throw "LLVM symbol typed source unavailable"
  let some abi := source.abi | throw "LLVM declaration source unavailable"
  let some names := abi.symbolNames | throw "LLVM codegen symbol attributes unavailable"
  let [declaration] := (names.declarations.filter (·.definition == raw)).toList
    | throw "LLVM codegen symbol declaration absent/ambiguous"
  return declaration.attributes.symbolName

end Miri.Input.SourceCallFacts
