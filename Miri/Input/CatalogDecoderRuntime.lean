import Miri.Input.Model.Catalogs
import Miri.Input.JsonReader
import Miri.Input.GenericArgsCodec

namespace Miri.Input.CatalogDecoder
open JsonReader Catalog

private abbrev R := Except String
private abbrev V := Slice
private def field (j : Object) (key : String) : R V := j.field key
private def str (j : Object) (key : String) : R String := do (← field j key).string
private def nat (j : Object) (key : String) : R Nat := do (← field j key).natural
private def bool (j : Object) (key : String) : R Bool := do (← field j key).boolean
private def arr (decode : V → R α) (j : V) : R (Array α) := do (← j.array).mapM decode
private def nullable (decode : V → R α) (j : V) : R (Option α) :=
  if j.isNull then pure none else some <$> decode j
private def opt (decode : V → R α) (j : Object) (key : String) : R (Option α) := do
  match ← j.optionalField key with
  | none => pure none
  | some value => some <$> decode value
private def expected (j : Object) (key value : String) : R Unit := do
  unless (← str j key) == value do throw s!"{key}: expected {value}"
private def environment (j : Object) : R Unit := expected j "typing_env" "fully_monomorphized"
private def digest (j : Object) (key : String) : R String := do
  let value ← str j key
  unless value.length == 64 && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do
    throw s!"invalid SHA256 evidence in {key}"
  return value
private def artifact (j : V) : R Artifact := do
  let j ← j.view
  return {
    path := ← str j "path", sha256 := ← digest j "sha256", sizeBytes := ← nat j "size_bytes"
    crateName := ← str j "crate_name", kind := ← str j "kind"
    withinSysroot := ← bool j "within_sysroot"
    sysrootRelativePath := ← nullable Slice.string (← field j "sysroot_relative_path") }
private def pass (j : V) : R (String × Bool) := do
  let values ← j.array
  unless values.size == 2 do throw "invalid MIR pass setting evidence"
  let some name := values[0]? | throw "MIR pass name missing"
  let some enabled := values[1]? | throw "MIR pass setting missing"
  return (← name.string, ← enabled.boolean)

def producerSettings (j : V) : R ProducerSettings := do
  let j ← j.view
  expected j "hash_algorithm" "sha256"
  return {
    sysrootPath := ← str j "sysroot_path", hashAlgorithm := "sha256"
    sysrootManifestSha256 := ← digest j "sysroot_manifest_sha256"
    loadedArtifactsManifestSha256 := ← digest j "loaded_artifacts_manifest_sha256"
    artifacts := ← arr artifact (← field j "artifacts")
    requestedCfgMiri := ← bool j "requested_cfg_miri"
    miriDefaultArgs := ← arr Slice.string (← field j "miri_default_args")
    rustcArgs := ← arr Slice.string (← field j "rustc_args")
    effectivePanicStrategy := ← str j "effective_panic_strategy"
    mirOptLevel := ← nullable Slice.natural (← field j "mir_opt_level")
    mirEnablePasses := ← arr pass (← field j "mir_enable_passes")
    mirPreserveUb := ← bool j "mir_preserve_ub"
    extraConstUbChecks := ← bool j "extra_const_ub_checks"
    alwaysEncodeMir := ← bool j "always_encode_mir"
    deduplicateDiagnostics := ← bool j "deduplicate_diagnostics"
    qualification := ← str j "qualification" }

private def runtimeCheck (j : V) : R (Miri.MIR.RuntimeChecks × Bool) := do
  let j ← j.view
  let kind ← match ← str j "kind" with
    | "ub_checks" => pure Miri.MIR.RuntimeChecks.UbChecks
    | "contract_checks" => pure .ContractChecks
    | "overflow_checks" => pure .OverflowChecks
    | _ => throw "unknown compiler runtime-check kind"
  return (kind, ← bool j "enabled")

def session (j : V) : R Session := do
  let j ← j.view
  let checks ← arr runtimeCheck (← field j "runtime_checks")
  let mut seen := #[]
  for (kind, _) in checks do
    unless !seen.contains kind do throw "duplicate compiler runtime-check query"
    seen := seen.push kind
  return {
    internalTargetFeatures := ← arr Slice.string (← field j "internal_target_features")
    isLikeWasm := ← bool j "is_like_wasm", targetArch := ← str j "target_arch"
    rootSpan := ← nat j "root_span", runtimeChecks := checks }

private def intrinsic (j : V) : R IntrinsicMetadata := do
  let j ← j.view
  return { mustOverride := ← bool j "must_be_overridden", fallbackIsSpec := ← bool j "fallback_is_spec" }
private def targetFeature (j : V) : R TargetFeature := do
  let j ← j.view
  return { name := ← str j "name", kind := ← str j "kind" }
private def runtimeInstance (j : V) : R RuntimeInstance := do
  let j ← j.view
  return {
    instanceId := ← nat j "instance_id", requiresCallerLocation := ← bool j "requires_caller_location"
    display := ← str j "display", inlineNever := ← bool j "inline_never"
    targetFeatures := ← arr targetFeature (← field j "target_features")
    isForeignItem := ← bool j "is_foreign_item", isClosureLike := ← bool j "is_closure_like"
    intrinsicMetadata := ← opt (nullable intrinsic) j "intrinsic_metadata"
    itemName := ← opt Slice.string j "item_name"
    codegenSymbolName := ← opt (nullable Slice.string) j "codegen_symbol_name"
    symbolName := ← opt Slice.string j "symbol_name" }
private def runtimeType (j : V) : R RuntimeType := do
  let j ← j.view
  environment j
  return {
    inputType := ← nat j "input_type_id", mutPointerType := ← nat j "mut_pointer_type"
    mutReferenceType := ← nat j "mut_reference_type", dropGlue := ← opt Slice.natural j "drop_glue" }
private def vtableRef (j : V) : R VtableRef := do
  let j ← j.view
  return {
    inputType := ← nat j "input_type"
    inputPredicates := ← arr Slice.natural (← field j "input_predicates"), queryId := ← nat j "query_id" }
private def runtimeVirtual (j : V) : R RuntimeVirtual := do
  let j ← j.view
  environment j
  return {
    originalInstance := ← nat j "original_instance_id", methodDefinition := ← nat j "method_definition"
    parentTrait := ← nat j "parent_trait", concreteType := ← nat j "concrete_type"
    rebasedArgs := ← GenericArgsCodec.decode (← field j "rebased_args")
    resolved := ← nat j "resolved", vtableQuery := ← vtableRef (← field j "vtable_query") }
private def escapeDefault (j : V) : R (DefinitionRef × Bool) := do
  let j ← j.view
  return (← nat j "definition", ← bool j "mir_available")
private def startup (j : V) : R Startup := do
  let j ← j.view
  return { noCore := ← bool j "no_core", coreEscapeDefault := ← opt escapeDefault j "core_escape_default" }

private def linkage (j : V) : R ImportLinkage := do
  let j ← j.view
  match ← str j "kind" with
  | "none" => pure .none
  | "external_weak" => pure (.externalWeak (← str j "raw"))
  | "other" => pure (.other (← str j "raw"))
  | _ => throw "unknown extern import linkage"
private def declaration (j : V) : R ExternDeclaration := do
  let j ← j.view
  environment j
  let mutability ← match ← str j "definition_mutability" with
    | "mutable" => pure MemoryMutability.mutable
    | "immutable" => pure .immutable
    | _ => throw "unknown extern definition mutability"
  return {
    definition := ← nat j "definition", symbol := ← str j "symbol", typeId := ← nat j "type"
    layoutId := ← nat j "layout", importLinkage := ← linkage (← field j "import_linkage")
    definitionMutability := mutability, typeIsFreeze := ← bool j "type_is_freeze"
    declIsMut := ← bool j "decl_is_mut" }
private def candidateFields (j : Object) : R ForeignCandidate := do
  return {
    iterationIndex := ← nat j "iteration_index", used := ← bool j "used", symbol := ← str j "symbol"
    definition := ← nat j "definition", explicitSymbol := ← bool j "explicit_symbol"
    crateIndex := ← nat j "crate_index", crateName := ← str j "crate_name", weak := ← bool j "weak"
    span := ← nat j "span", definitionKind := ← str j "definition_kind"
    compilerBuiltins := ← bool j "compiler_builtins", instanceId := ← opt Slice.natural j "instance_id" }
private def candidate (j : V) : R ForeignCandidate := do
  candidateFields (← j.view)
private def selectedExport (j : V) : R SelectedExport := do
  let j ← j.view
  let symbol ← str j "symbol"
  if let some resolution ← j.optionalField "resolution" then
    unless (← resolution.string) == "ambiguous" do throw "unknown foreign export resolution"
    return .ambiguous symbol (← str j "reason")
  let kind ← str j "kind"
  let definition ← nat j "definition"
  if kind == "static" then
    return .static symbol definition (← declaration (← field j "declaration")) (← nat j "allocation")
  return .other symbol kind definition (← nullable Slice.natural (← field j "instance_id"))
private def fallback (j : V) : R ForeignFallback := do
  let j ← j.view
  if let some resolution ← j.optionalField "resolution" then
    unless (← resolution.string) == "ambiguous" do throw "unknown foreign fallback resolution"
    return .ambiguous (← str j "symbol") (← str j "reason")
  return .candidate (← candidateFields j)
private def allocatorShim (j : V) : R (String × AllocatorTarget) := do
  let j ← j.view
  let target ← (← field j "target").view
  let target ← match ← str target "kind" with
    | "special" => pure (AllocatorTarget.special (← str target "method"))
    | "redirect" => pure (.redirect (← str target "symbol"))
    | _ => throw "unknown allocator shim target"
  return (← str j "symbol", target)
private def foreignSymbols (j : V) : R ForeignSymbols := do
  let j ← j.view
  let target ← (← field j "target").view
  let statics ← (← j.optionalField "extern_statics").mapM Slice.view
  let declarations ← match statics with
    | none => pure none
    | some value => environment value; some <$> arr declaration (← field value "declarations")
  let exports ← match statics with
    | none => pure none
    | some value => some <$> arr selectedExport (← field value "selected_exported")
  return {
    os := ← str target "os", env := ← str target "env", binaryFormat := ← str target "binary_format"
    families := ← arr Slice.string (← field target "families")
    noAllocShimSymbol := ← str j "no_alloc_shim_symbol"
    allocatorShims := ← arr allocatorShim (← field j "allocator_shims")
    exportedCandidates := ← opt (arr candidate) j "exported_candidates"
    selectedForeignFallbacks := ← opt (arr fallback) j "selected_foreign_fallbacks"
    externDeclarations := declarations, selectedExports := exports }

def runtime (j : V) : R Runtime := do
  let j ← j.view
  return {
    startup := ← opt startup j "startup", types := ← arr runtimeType (← field j "types")
    virtualQueries := ← arr runtimeVirtual (← field j "virtual")
    instances := ← arr runtimeInstance (← field j "instances")
    foreignSymbols := ← foreignSymbols (← field j "foreign_symbols") }

private def targetPointer (j : V) : R TargetPointerSpec := do
  let j ← j.view
  return {
    pointerSizeBytes := ← nat j "pointer_size_bytes"
    pointerAlignBytes := ← nat j "pointer_align_bytes"
    pointerOffsetBytes := ← nat j "pointer_offset_bytes"
    isFat := ← bool j "is_fat" }
private def targetSpace (j : V) : R TargetAddressSpace := do
  let j ← j.view
  return {
    addressSpace := ← nat j "address_space"
    spec := ← targetPointer (← field j "spec")
    objectSizeBoundBytes := ← nullable Slice.natural (← field j "object_size_bound_bytes") }
private def vectorAlign (j : V) : R (Nat × Nat) := do
  let j ← j.view
  return (← nat j "size_bytes", ← nat j "align_bytes")

def targetDataLayout (j : V) : R TargetDataLayoutEvidence := do
  let j ← j.view
  return {
    evidencePath := ← str j "evidence_path"
    llvmDataLayout := ← str j "llvm_data_layout"
    privateInventoryEvidence := ← str j "private_inventory_evidence"
    alignmentEvidence := ← str j "alignment_evidence"
    endian := ← str j "endian"
    pointerWidthBits := ← nat j "pointer_width_bits"
    objectSizeBoundBytes := ← nullable Slice.natural (← field j "object_size_bound_bytes")
    i1AlignBytes := ← nat j "i1_align_bytes"
    i8AlignBytes := ← nat j "i8_align_bytes"
    i16AlignBytes := ← nat j "i16_align_bytes"
    i32AlignBytes := ← nat j "i32_align_bytes"
    i64AlignBytes := ← nat j "i64_align_bytes"
    i128AlignBytes := ← nat j "i128_align_bytes"
    f16AlignBytes := ← nat j "f16_align_bytes"
    f32AlignBytes := ← nat j "f32_align_bytes"
    f64AlignBytes := ← nat j "f64_align_bytes"
    f128AlignBytes := ← nat j "f128_align_bytes"
    aggregateAlignBytes := ← nat j "aggregate_align_bytes"
    vectorAlign := ← arr vectorAlign (← field j "vector_align")
    defaultAddressSpace := ← nat j "default_address_space"
    defaultAddressSpacePointerSpec := ← targetPointer (← field j "default_address_space_pointer_spec")
    addressSpaceInfo := ← arr targetSpace (← field j "address_space_info")
    instructionAddressSpace := ← nat j "instruction_address_space"
    cEnumMinSize := ← str j "c_enum_min_size" }

end Miri.Input.CatalogDecoder
