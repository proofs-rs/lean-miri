import Miri.Input.Reader.Catalog
import Miri.Input.CompilerTables

namespace Miri.Input.Reader
open Lean

def Catalog.readRuntimeInstances (catalog : Catalog) (count : Nat) : Except String (Array RuntimeInstanceData) := do
  let query ← catalog.field catalog.root "compiler_runtime_queries" "$"
  let values ← catalog.array (← catalog.field query "instances" "runtime queries") "runtime instances"
  values.mapIdxM fun index input => do
    let path := s!"runtime instances[{index}]"
    let field := fun key => catalog.field input key path
    let instanceId ← catalog.natural (← field "instance_id") path
    unless instanceId < count do throw s!"{path}: invalid instance ID {instanceId}"
    let itemName : Except String String := do
      let query ← field "item_name"
      catalog.requireSupported query path
      catalog.string (← catalog.field query "value" path) path
    let intrinsic : Except String (Option IntrinsicData) := do
      let query ← field "intrinsic_metadata"
      catalog.requireSupported query path
      let value ← catalog.inspect (← catalog.field query "value" path) path
      if value == .null then pure none else do
        let required ← catalog.boolean (← catalog.field value "must_be_overridden" path) path
        let fallback ← catalog.boolean (← catalog.field value "fallback_is_spec" path) path
        return some ⟨required,fallback⟩
    let symbolName : Except String String := do
      let query ← field "symbol_name"
      catalog.requireSupported query path
      catalog.string (← catalog.field query "value" path) path
    let codegenSymbolName : Except String (Option String) := do
      let query ← field "codegen_symbol_name"
      catalog.requireSupported query path
      let value ← catalog.inspect (← catalog.field query "value" path) path
      if value == .null then pure none else some <$> catalog.string value path
    let targetFeatures : Except String (Array (String × Bool)) := do
      let features ← catalog.array (← field "target_features") path
      features.mapM fun feature => do
        let name ← catalog.string (← catalog.field feature "name" path) path
        let implied ← match ← catalog.string (← catalog.field feature "kind" path) path with
          | "implied" => pure true | "enabled" | "forced" => pure false
          | _ => throw s!"{path}: unknown compiler target-feature kind"
        pure (name,implied)
    let display ← catalog.string (← field "display") path
    let callerLocation ← catalog.boolean (← field "requires_caller_location") path
    let inlineNever ← catalog.boolean (← field "inline_never") path
    let foreignItem ← catalog.boolean (← field "is_foreign_item") path
    let closureLike ← catalog.boolean (← field "is_closure_like") path
    return ⟨instanceId,display,callerLocation,inlineNever,itemName,intrinsic,
      foreignItem,closureLike,symbolName,codegenSymbolName,targetFeatures⟩

end Miri.Input.Reader
