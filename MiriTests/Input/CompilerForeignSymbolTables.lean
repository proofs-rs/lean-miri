import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.CompilerFactAdapters

/-! Parser regression for compiler foreign symbol tables, including callable
exports sharing a lowering context. The fixtures exercise raw `foreign_symbols`
JSON through `prepare`, rather than preconstructed Prepared entries. -/

open Lean Miri.Input Miri.Interpreter

private def document (raw : Json) : ImportDocument :=
  { producer := ⟨"miri", "rustc", "version", "target"⟩
    types := #[]
    allocations := #[]
    instances := #[]
    selectedScope := none
    functionAbis := #[]
    bodies := #[]
    raw := raw }

private def target : Miri.ABI.RuntimeTargetDataLayout := Id.run do
  let size : Miri.ABI.Size := ⟨8⟩
  let ptr : Miri.ABI.PointerSpec := ⟨size, .ONE, size, false⟩
  return ⟨⟨.little, .w64⟩, .ONE, .ONE, .ONE, .ONE, .ONE, .ONE,
    .ONE, .ONE, .ONE, .ONE, .ONE, #[], .ZERO, ptr, #[], .ZERO, .I32⟩

private def rawSymbols (allocators : Json) (candidates : Array Json := #[]) : Json :=
  Json.mkObj [("instances", .arr (#[0,1].map fun id => Json.mkObj [
    ("instance_id", toJson id), ("kind", .str "identity_only"), ("def_id", toJson id), ("instance_kind", Json.mkObj [
      ("kind", .str "item"), ("def_id", toJson id)]), ("generic_args", .arr #[])])),
    ("compiler_runtime_queries", Json.mkObj [("foreign_symbols",
    Json.mkObj [
      ("no_alloc_shim_symbol", toJson "__no_alloc"),
      ("exported_candidates", Json.arr candidates),
      ("allocator_shims", allocators)
    ])])]

private def allocator (name : String) (target : Json) : Json :=
  Json.mkObj [("symbol", toJson name), ("target", target)]

private def special (method : String) : Json :=
  Json.mkObj [("kind", toJson "special"), ("method", toJson method)]

private def redirect (symbol : String) : Json :=
  Json.mkObj [("kind", toJson "redirect"), ("symbol", toJson symbol)]

private def prepare (raw : Json) (definitions : Array DefinitionId := #[]) :
    Except String CompilerForeignSymbolTables.Prepared := do
  let instanceRows ← ((raw.getObjVal? "instances").bind Json.getArr?)
  let instanceNodes ← instanceRows.mapIdxM fun index row => DecoderValues.parseInstance row s!"instances[{index}]"
  let base := document raw
  let source : ImportDocument := {
    base with
    definitions := definitions
    instances := instanceNodes
    spans := #[{
      originalPayload := "symbol"
      lo := 0
      hi := 1
      start := ⟨1,0⟩
      «end» := ⟨1,1⟩
      context := "root"
      file := "test.rs" }] }
  let program : LoweredProgram := ⟨⟨#[], #[], definitions, #[]⟩, #[], #[], #[], source⟩
  let runtime : RuntimeMetadata := {
    source := source
    target := target
  }
  let context : CompilerFacts.Context := {
    runtime := runtime
    program := program
  }
  let facts : CompilerFactAdapters.Prepared := { context := context, patterns := #[], castTypes := #[], obligations := #[] }
  let instances : CompilerVTableRuntime.Prepared := ⟨facts, #[]⟩
  CompilerForeignSymbolTables.prepare instances

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
  ("instance_id", toJson definition),
  ("span", toJson (0 : Nat)),
  ("symbol", toJson s!"callable{iteration}"), ("explicit_symbol", toJson true),
  ("crate_index", toJson (1 : Nat)), ("crate_name", toJson "test"),
  ("weak", toJson false), ("compiler_builtins", toJson false)]

private def callableDefinitions : Array DefinitionId := #[⟨1,7⟩, ⟨1,8⟩]

-- Two callable identities share the lowering context while retaining distinct
-- dense definitions and the original finalized-table validation.
#guard match prepare (rawSymbols (.arr #[]) #[callableCandidate 0 0, callableCandidate 1 1])
    callableDefinitions with
  | .error _ => false
  | .ok prepared =>
      prepared.candidates.size == 2 &&
      (prepared.candidates[0]?.bind (·.fnInstance)) == some 0 &&
      (prepared.candidates[1]?.bind (·.fnInstance)) == some 1

#guard match prepare (rawSymbols (.arr #[]) #[callableCandidate 0 0, callableCandidate 1 999])
    callableDefinitions with
  | .error message => message == "compiler instance ID 999 out of bounds"
  | .ok _ => false
