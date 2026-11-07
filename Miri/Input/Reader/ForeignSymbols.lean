import Miri.Input.Reader.Instances

namespace Miri.Input.Reader.ForeignSymbolReader
open Lean Miri.Interpreter
abbrev Decode := MIRReader.Decode

private def compilerValue (catalog : Catalog) (query : Json) (path : String) : Except String Json := do
  unless (← catalog.string (← catalog.field query "status" path) path) == "supported" do
    let reason := (do catalog.string (← catalog.field query "reason" path) path).toOption.getD
      "compiler query did not provide a reason"
    throw s!"compiler foreign-symbol query unresolved: {reason}"
  catalog.field query "value" path

private def exportKind (value : String) : Except String ForeignItems.ExportKind :=
  match value with
  | "function" => pure .function
  | "associated_function" => pure .associatedFunction
  | "static" => pure .staticItem
  | "other" => pure .other
  | _ => throw s!"unknown exported symbol definition kind `{value}`"

private def allocatorTarget (catalog : Catalog) (record : Json) (path : String) : Except String ForeignAllocatorTarget := do
  let target ← catalog.field record "target" path
  match ← catalog.string (← catalog.field target "kind" path) path with
  | "redirect" => return .redirect (← catalog.string (← catalog.field target "symbol" path) path)
  | "special" =>
    let method ← catalog.string (← catalog.field target "method" path) path
    match method with
    | "alloc" => return .special .Alloc
    | "alloc_zeroed" => return .special .AllocZeroed
    | "dealloc" => return .special .Dealloc
    | "realloc" => return .special .Realloc
    | _ => throw s!"unknown compiler special allocator method `{method}`"
  | kind => throw s!"unknown compiler allocator target `{kind}`"

private def queries (catalog : Catalog) (typeCount : Nat) : Decode ForeignSymbolsData := do
  let path := "$.compiler_runtime_queries.foreign_symbols"
  let source ← catalog.field (← catalog.field catalog.root "compiler_runtime_queries" "$") "foreign_symbols" path
  let field := fun key => catalog.field source key path
  let noAlloc ← field "no_alloc_shim_symbol"
  unless (← catalog.string (← catalog.field noAlloc "status" path) path) == "supported" do
    throw "compiler no-allocation shim symbol unresolved"
  let noAllocName ← catalog.string (← catalog.field noAlloc "value" path) path
  let records ← catalog.array (← compilerValue catalog (← field "exported_candidates") path) path
  let mut candidates := #[]
  let mut previousIndex : Option Nat := none
  for (record,position) in records.toList.zipIdx do
    let path := s!"{path}.exported_candidates[{position}]"
    let field := fun key => catalog.field record key path
    let text := fun key => do catalog.string (← field key) path
    let natural := fun key => do catalog.natural (← field key) path
    let boolean := fun key => do catalog.boolean (← field key) path
    let index ← natural "iteration_index"
    if let some previous := previousIndex then
      unless previous < index do throw "exported symbol iterator order is missing or inconsistent"
    previousIndex := some index
    let kind ← exportKind (← text "definition_kind")
    let callee ← if kind == .function || kind == .associatedFunction then do
        let before ← get
        let (decoded,next) ← (InstanceReader.read catalog typeCount (← field "callable_identity") path).run before
        unless next.compiler.definitions == before.compiler.definitions &&
            next.compiler.typeConstants == before.compiler.typeConstants do
          throw "exported callable identity is absent from finalized compiler tables"
        set next
        pure (some decoded)
      else pure none
    let span ← field "span"
    let candidate : ForeignSymbolCandidate := {
      symbol := ← text "symbol"
      explicitSymbol := ← boolean "explicit_symbol"
      fnInstance := callee
      crateIndex := ← natural "crate_index"
      crateName := ← text "crate_name"
      weak := ← boolean "weak"
      spanLo := ← catalog.natural (← catalog.field span "lo" path) path
      spanHi := ← catalog.natural (← catalog.field span "hi" path) path
      kind
      compilerBuiltins := ← boolean "compiler_builtins" }
    candidates := candidates.push candidate
  let records ← catalog.array (← compilerValue catalog (← field "allocator_shims") path) path
  let mut allocators := #[]
  for record in records do
    let symbol ← catalog.string (← catalog.field record "symbol" path) path
    if allocators.any (·.symbol == symbol) then throw s!"duplicate compiler allocator shim symbol `{symbol}`"
    allocators := allocators.push (⟨symbol,← allocatorTarget catalog record path⟩ : ForeignAllocatorEntry)
  return ⟨noAllocName,candidates,allocators⟩

def read (catalog : Catalog) (typeCount : Nat) : Decode (Except String ForeignSymbolsData) := do
  let original ← get
  match (queries catalog typeCount).run original with
  | .error reason => pure (.error reason)
  | .ok (value,next) => set next; pure (.ok value)

end Miri.Input.Reader.ForeignSymbolReader
