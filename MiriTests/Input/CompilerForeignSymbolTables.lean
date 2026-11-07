import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.Reader.ForeignSymbols

/-! Parser regression for typed compiler foreign symbol tables, including
callable exports checked against the finalized definition table. -/

open Lean Miri.Input Miri.Interpreter

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

private def prepare (raw : Json) (definitions : Array DefinitionId := #[]) (nodes : Array Json := #[]) :
    Except String CompilerForeignSymbolTables.Prepared := do
  let .obj fields := raw | throw "expected object"
  let input := Json.mkObj (("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", Json.arr nodes)]) :: fields.toList)
  let catalog ← Reader.Catalog.parse input
  let (result,_) ← (Reader.ForeignSymbolReader.read catalog 0).run
    (Reader.MIRReader.initial catalog.nodes.size {definitions})
  result

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

-- A shared array and shared allocator target are read only at the boundary.
#guard match prepare (rawSymbols (Json.mkObj [("$lean_miri_shared_ref",toJson (1 : Nat))])) #[]
    #[special "alloc", Json.arr #[allocator "shared_alloc"
      (Json.mkObj [("$lean_miri_shared_ref",toJson (0 : Nat))])]] with
  | .ok prepared => allocatorIs prepared "shared_alloc" (.special .Alloc)
  | .error _ => false
