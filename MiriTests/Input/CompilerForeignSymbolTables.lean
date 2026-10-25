import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.CompilerFactAdapters

/-! Parser regression for compiler foreign symbol tables, including callable
exports sharing a lowering context. The fixtures exercise raw `foreign_symbols`
JSON through `prepare`, rather than preconstructed Prepared entries. -/

open Lean Miri.Input Miri.Interpreter

private def document (raw : Json) : ImportDocument :=
  { producer := ⟨"miri", "rustc", "version", "target"⟩
    completenessStatus := .supported
    types := #[]
    allocations := #[]
    instances := #[]
    selectedScope := none
    functionAbis := #[]
    bodies := #[]
    typedTree := .scalar .null
    obligations := #[]
    raw := raw }

private def target : Miri.ABI.RuntimeTargetDataLayout := Id.run do
  let size : Miri.ABI.Size := ⟨8⟩
  let ptr : Miri.ABI.PointerSpec := ⟨size, .ONE, size, false⟩
  return ⟨⟨.little, .w64⟩, .ONE, .ONE, .ONE, .ONE, .ONE, .ONE,
    .ONE, .ONE, .ONE, .ONE, .ONE, #[], .ZERO, ptr, #[], .ZERO, .I32⟩

private def rawSymbols (allocators : Json) (candidates : Array Json := #[]) : Json :=
  Json.mkObj [("compiler_runtime_queries", Json.mkObj [("foreign_symbols",
    Json.mkObj [
      ("no_alloc_shim_symbol", Json.mkObj [("status", toJson "supported"), ("value", toJson "__no_alloc")]),
      ("exported_candidates", Json.mkObj [("status", toJson "supported"), ("value", Json.arr candidates)]),
      ("allocator_shims", Json.mkObj [("status", toJson "supported"), ("value", allocators)])
    ])])]

private def allocator (name : String) (target : Json) : Json :=
  Json.mkObj [("symbol", toJson name), ("target", target)]

private def special (method : String) : Json :=
  Json.mkObj [("kind", toJson "special"), ("method", toJson method)]

private def redirect (symbol : String) : Json :=
  Json.mkObj [("kind", toJson "redirect"), ("symbol", toJson symbol)]

private def prepare (raw : Json) (definitions : Array DefinitionId := #[]) :
    Except String CompilerForeignSymbolTables.Prepared := Id.run do
  let source := document raw
  let program : LoweredProgram := ⟨⟨#[], #[], definitions, #[]⟩, #[], #[], #[], source⟩
  let runtime : RuntimeMetadata := {
    source := source.toCore
    target := target
    layouts := #[]
  }
  let context : CompilerFacts.Context := {
    runtime := RuntimeMetadata.Indexed.ofMetadata runtime
    program := program
  }
  let facts : CompilerFactAdapters.Prepared := ⟨context, #[], #[], #[], #[]⟩
  let instances : CompilerVTableRuntime.Prepared := ⟨facts, #[], #[]⟩
  return CompilerForeignSymbolTables.prepare instances

private def allocatorRows : Array Json := #[
  allocator "_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc" (special "alloc"),
  allocator "__alloc_zeroed" (special "alloc_zeroed"),
  allocator "__dealloc" (special "dealloc"),
  allocator "__realloc" (special "realloc"),
  allocator "__redirect" (redirect "real_allocator")
]

private def decoded := prepare (rawSymbols (Json.arr allocatorRows))

private def allocatorIs (prepared : CompilerForeignSymbolTables.Prepared)
    (symbol : String) (expected : ForeignItems.AllocatorSymbol CallInstance) : Bool :=
  match CompilerForeignSymbolTables.allocatorSymbol prepared symbol, expected with
  | some (.special actual), .special wanted => actual == wanted
  | some (.redirect actual), .redirect wanted => actual == wanted
  | _, _ => false

#guard match decoded with
  | .error _ => false
  | .ok prepared =>
      allocatorIs prepared "_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc" (.special .Alloc) &&
      allocatorIs prepared "__alloc_zeroed" (.special .AllocZeroed) &&
      allocatorIs prepared "__dealloc" (.special .Dealloc) &&
      allocatorIs prepared "__realloc" (.special .Realloc) &&
      allocatorIs prepared "__redirect" (.redirect "real_allocator") &&
      (CompilerForeignSymbolTables.allocatorSymbol prepared "__missing").isNone

#guard match prepare (rawSymbols (Json.arr (allocatorRows.push
    (allocator "_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc" (special "alloc"))))) with
  | .error message => message == "duplicate compiler allocator shim symbol `_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc`"
  | .ok _ => false

private def callableCandidate (iteration definition : Nat) : Json := Json.mkObj [
  ("iteration_index", toJson iteration),
  ("definition_kind", toJson "function"),
  ("callable_identity", Json.mkObj [
    ("instance_kind", Json.mkObj [("kind", toJson "item"),
      ("def_id", Json.mkObj [("crate", toJson (1 : Nat)), ("index", toJson definition)])]),
    ("generic_args", Json.arr #[])]),
  ("span", Json.mkObj [("lo", toJson iteration), ("hi", toJson (iteration + 1))]),
  ("symbol", toJson s!"callable{iteration}"), ("explicit_symbol", toJson true),
  ("crate_index", toJson (1 : Nat)), ("crate_name", toJson "test"),
  ("weak", toJson false), ("compiler_builtins", toJson false)]

private def callableDefinitions : Array DefinitionId := #[⟨1,7⟩, ⟨1,8⟩]

-- Two callable identities share the lowering context while retaining distinct
-- dense definitions and the original finalized-table validation.
#guard match prepare (rawSymbols (.arr #[]) #[callableCandidate 0 7, callableCandidate 1 8])
    callableDefinitions with
  | .error _ => false
  | .ok prepared =>
      prepared.candidates.size == 2 &&
      ((prepared.candidates[0]?.bind (·.fnInstance)).map (·.defId)) == some 0 &&
      ((prepared.candidates[1]?.bind (·.fnInstance)).map (·.defId)) == some 1

#guard match prepare (rawSymbols (.arr #[]) #[callableCandidate 0 7, callableCandidate 1 999])
    callableDefinitions with
  | .error message => message == "exported callable identity is absent from finalized compiler tables"
  | .ok _ => false
