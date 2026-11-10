import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.CompilerFactAdapters

/-! Typed compiler foreign-symbol fixtures exercise allocator selection,
canonical callable identities, and duplicate/order rejection in preparation. -/

open Lean Miri.Input Miri.Interpreter

private def unusedSettings : Catalog.ProducerSettings := {
  sysrootPath := "", hashAlgorithm := "sha256", sysrootManifestSha256 := ""
  loadedArtifactsManifestSha256 := "", artifacts := #[], requestedCfgMiri := false
  miriDefaultArgs := #[], rustcArgs := #[], effectivePanicStrategy := "abort", mirOptLevel := none
  mirEnablePasses := #[], mirPreserveUb := false, extraConstUbChecks := false
  alwaysEncodeMir := false, deduplicateDiagnostics := false, qualification := "fixture" }

private def unusedPrimitives : Catalog.Primitives := {
  u8 := 0, u16 := 0, u32 := 0, u64 := 0, u128 := 0
  i8 := 0, i16 := 0, i32 := 0, i64 := 0, i128 := 0, bool := 0
  pointerTagInteger := 0, usize := 0, isize := 0, unit := 0
  unitPointerConst := 0, unitPointerMut := 0, immU8Pointer := 0, immU8PointerPointer := 0
  typeNameResultType := 0, callerLocationType := none, orderingEnum := none }

private def document (symbols : Catalog.ForeignSymbols) : ImportDocument := {
  producer := ⟨"miri", "rustc", "version", "target"⟩
  types := #[], allocations := #[], instances := #[], selectedScope := none
  functionAbis := #[], bodies := #[], producerSettings := unusedSettings
  queries := {
    session := ⟨#[], false, "test", 0, #[]⟩
    runtime := ⟨none, #[], #[], #[], symbols⟩
    frameMetadata := ⟨0, #[]⟩, instanceAbis := #[]
    functionFacts := ⟨#[], #[], #[]⟩, casts := #[], typeNames := #[], panic := #[]
    nativeSignatures := #[], retag := #[], covariance := #[]
    globalBytes := ⟨0, 0, #[], #[]⟩, callerLocations := #[]
    main := ⟨none, none, none, #[], none⟩, primitives := unusedPrimitives
    vtables := #[], namedTypes := none, shimAbis := none, namedShimAbis := none
    libcTypeLayouts := none, windowsTypeLayouts := none, namedConstants := none, namedStatics := none } }

private def target : Miri.ABI.RuntimeTargetDataLayout := Id.run do
  let size : Miri.ABI.Size := ⟨8⟩
  let ptr : Miri.ABI.PointerSpec := ⟨size, .ONE, size, false⟩
  return ⟨⟨.little, .w64⟩, .ONE, .ONE, .ONE, .ONE, .ONE, .ONE,
    .ONE, .ONE, .ONE, .ONE, .ONE, #[], .ZERO, ptr, #[], .ZERO, .I32⟩

private def symbols (allocators : Array (String × Catalog.AllocatorTarget))
    (candidates : Array Catalog.ForeignCandidate := #[]) : Catalog.ForeignSymbols := {
  os := "test", env := "", binaryFormat := "", families := #[]
  noAllocShimSymbol := "__no_alloc", allocatorShims := allocators
  exportedCandidates := some candidates, selectedForeignFallbacks := none
  externDeclarations := none, selectedExports := none }

private def instanceNode (id : Nat) : InstanceNode := {
  id, kind := .identityOnly, instanceKind := .Item id, genericArgs := #[]
  defPath := none, definitionId := some id, bodyInstantiation := none
  bodyTemplateIsPolymorphic := none, instanceArgsAreMonomorphic := none
  bodyId := none, promotedBodies := #[] }

private def prepare (symbols : Catalog.ForeignSymbols) (definitions : Array DefinitionId := #[]) :
    Except String CompilerForeignSymbolTables.Prepared := do
  let base := document symbols
  let source : ImportDocument := {
    base with
    definitions, instances := #[instanceNode 0, instanceNode 1]
    spans := #[{ lo := 0, hi := 1, start := ⟨1,0⟩, «end» := ⟨1,1⟩, context := "root", file := "test.rs" }] }
  let program : LoweredProgram := ⟨⟨#[], #[], definitions, #[]⟩, #[], #[], #[], source⟩
  let runtime : RuntimeMetadata := { source, target }
  let context : CompilerFacts.Context := { runtime, program }
  let facts : CompilerFactAdapters.Prepared := { context, patterns := #[], castTypes := #[], obligations := #[] }
  CompilerForeignSymbolTables.prepare ⟨facts, #[]⟩

private def allocatorRows : Array (String × Catalog.AllocatorTarget) := #[
  ("_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc", .special "alloc"),
  ("__alloc_zeroed", .special "alloc_zeroed"),
  ("__dealloc", .special "dealloc"),
  ("__realloc", .special "realloc"),
  ("__redirect", .redirect "real_allocator") ]

private def decoded := prepare (symbols allocatorRows)

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

#guard match prepare (symbols (allocatorRows.push
    ("_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc", .special "alloc"))) with
  | .error message => message == "duplicate compiler allocator shim symbol `_RNvCsaeuD6Zm55dc_7___rustc12___rust_alloc`"
  | .ok _ => false

private def callableCandidate (iteration definition : Nat) : Catalog.ForeignCandidate := {
  iterationIndex := iteration, used := true, definitionKind := "function"
  instanceId := some definition, definition, span := 0
  symbol := s!"callable{iteration}", explicitSymbol := true
  crateIndex := 1, crateName := "test", weak := false, compilerBuiltins := false }

private def callableDefinitions : Array DefinitionId := #[⟨1,7⟩, ⟨1,8⟩]

-- Two callable identities share the lowering context while retaining distinct
-- dense definitions and the original finalized-table validation.
#guard match prepare (symbols #[] #[callableCandidate 0 0, callableCandidate 1 1])
    callableDefinitions with
  | .error _ => false
  | .ok prepared =>
      prepared.candidates.size == 2 &&
      (prepared.candidates[0]?.bind (·.fnInstance)) == some 0 &&
      (prepared.candidates[1]?.bind (·.fnInstance)) == some 1

#guard match prepare (symbols #[] #[callableCandidate 0 0, callableCandidate 1 999])
    callableDefinitions with
  | .error message => message == "compiler instance ID 999 out of bounds"
  | .ok _ => false
