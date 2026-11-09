import Miri.Input.Model.Catalogs
import Miri.Input.JsonReader
import Miri.Input.GenericArgsCodec

/- Runtime query payloads contain no layout-dependent constants, so their
forward parsers construct the final typed records directly. -/
namespace Miri.Input.CatalogDecoder
open JsonReader Catalog

private def need (value : Option α) (name : String) : Parser α :=
  match value with
  | some value => pure value
  | none => fail s!"missing field `{name}`"

private def expectedString (expected : String) : Parser String := do
  let value ← string
  unless value == expected do fail s!"expected `{expected}`"
  pure value

private def digest : Parser String := do
  let value ← string
  unless value.length == 64 && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do
    fail "invalid SHA256 evidence"
  pure value

private structure artifactFields where
  path : Option (String) := none
  sha256 : Option (String) := none
  sizeBytes : Option (Nat) := none
  crateName : Option (String) := none
  kind : Option (String) := none
  withinSysroot : Option (Bool) := none
  sysrootRelativePath : Option (Option String) := none

private def artifact : Parser (Artifact) := do
  let fields ← object ({} : artifactFields) fun fields key => do
    match key with
    | "path" => return { fields with path := some (← string) }
    | "sha256" => return { fields with sha256 := some (← digest) }
    | "size_bytes" => return { fields with sizeBytes := some (← natural) }
    | "crate_name" => return { fields with crateName := some (← string) }
    | "kind" => return { fields with kind := some (← string) }
    | "within_sysroot" => return { fields with withinSysroot := some (← boolean) }
    | "sysroot_relative_path" => return { fields with sysrootRelativePath := some (← nullable string) }
    | _ => skipValue; pure fields
  let path ← need fields.path "path"
  let sha256 ← need fields.sha256 "sha256"
  let sizeBytes ← need fields.sizeBytes "size_bytes"
  let crateName ← need fields.crateName "crate_name"
  let kind ← need fields.kind "kind"
  let withinSysroot ← need fields.withinSysroot "within_sysroot"
  let sysrootRelativePath ← need fields.sysrootRelativePath "sysroot_relative_path"
  return {
    path, sha256, sizeBytes, crateName, kind, withinSysroot, sysrootRelativePath }

private def passSetting : Parser (String × Bool) := do
  Std.Internal.Parsec.String.skipChar '['; Std.Internal.Parsec.String.ws
  let name ← string
  Std.Internal.Parsec.String.ws; Std.Internal.Parsec.String.skipChar ','; Std.Internal.Parsec.String.ws
  let enabled ← boolean
  Std.Internal.Parsec.String.ws; Std.Internal.Parsec.String.skipChar ']'
  pure (name, enabled)

private structure producerSettingsFields where
  sysrootPath : Option (String) := none
  hashAlgorithm : Option (String) := none
  sysrootManifestSha256 : Option (String) := none
  loadedArtifactsManifestSha256 : Option (String) := none
  artifacts : Option (Array (Artifact)) := none
  requestedCfgMiri : Option (Bool) := none
  miriDefaultArgs : Option (Array (String)) := none
  rustcArgs : Option (Array (String)) := none
  effectivePanicStrategy : Option (String) := none
  mirOptLevel : Option (Option Nat) := none
  mirEnablePasses : Option (Array (String × Bool)) := none
  mirPreserveUb : Option (Bool) := none
  extraConstUbChecks : Option (Bool) := none
  alwaysEncodeMir : Option (Bool) := none
  deduplicateDiagnostics : Option (Bool) := none
  qualification : Option (String) := none

def producerSettings : Parser (ProducerSettings) := do
  let fields ← object ({} : producerSettingsFields) fun fields key => do
    match key with
    | "sysroot_path" => return { fields with sysrootPath := some (← string) }
    | "hash_algorithm" => return { fields with hashAlgorithm := some (← expectedString "sha256") }
    | "sysroot_manifest_sha256" => return { fields with sysrootManifestSha256 := some (← digest) }
    | "loaded_artifacts_manifest_sha256" => return { fields with loadedArtifactsManifestSha256 := some (← digest) }
    | "artifacts" => return { fields with artifacts := some (← array (artifact)) }
    | "requested_cfg_miri" => return { fields with requestedCfgMiri := some (← boolean) }
    | "miri_default_args" => return { fields with miriDefaultArgs := some (← array (string)) }
    | "rustc_args" => return { fields with rustcArgs := some (← array (string)) }
    | "effective_panic_strategy" => return { fields with effectivePanicStrategy := some (← string) }
    | "mir_opt_level" => return { fields with mirOptLevel := some (← nullable natural) }
    | "mir_enable_passes" => return { fields with mirEnablePasses := some (← array (passSetting)) }
    | "mir_preserve_ub" => return { fields with mirPreserveUb := some (← boolean) }
    | "extra_const_ub_checks" => return { fields with extraConstUbChecks := some (← boolean) }
    | "always_encode_mir" => return { fields with alwaysEncodeMir := some (← boolean) }
    | "deduplicate_diagnostics" => return { fields with deduplicateDiagnostics := some (← boolean) }
    | "qualification" => return { fields with qualification := some (← string) }
    | _ => skipValue; pure fields
  let sysrootPath ← need fields.sysrootPath "sysroot_path"
  let hashAlgorithm ← need fields.hashAlgorithm "hash_algorithm"
  let sysrootManifestSha256 ← need fields.sysrootManifestSha256 "sysroot_manifest_sha256"
  let loadedArtifactsManifestSha256 ← need fields.loadedArtifactsManifestSha256 "loaded_artifacts_manifest_sha256"
  let artifacts ← need fields.artifacts "artifacts"
  let requestedCfgMiri ← need fields.requestedCfgMiri "requested_cfg_miri"
  let miriDefaultArgs ← need fields.miriDefaultArgs "miri_default_args"
  let rustcArgs ← need fields.rustcArgs "rustc_args"
  let effectivePanicStrategy ← need fields.effectivePanicStrategy "effective_panic_strategy"
  let mirOptLevel ← need fields.mirOptLevel "mir_opt_level"
  let mirEnablePasses ← need fields.mirEnablePasses "mir_enable_passes"
  let mirPreserveUb ← need fields.mirPreserveUb "mir_preserve_ub"
  let extraConstUbChecks ← need fields.extraConstUbChecks "extra_const_ub_checks"
  let alwaysEncodeMir ← need fields.alwaysEncodeMir "always_encode_mir"
  let deduplicateDiagnostics ← need fields.deduplicateDiagnostics "deduplicate_diagnostics"
  let qualification ← need fields.qualification "qualification"
  return {
    sysrootPath, hashAlgorithm, sysrootManifestSha256, loadedArtifactsManifestSha256, artifacts, requestedCfgMiri, miriDefaultArgs, rustcArgs, effectivePanicStrategy, mirOptLevel, mirEnablePasses, mirPreserveUb, extraConstUbChecks, alwaysEncodeMir, deduplicateDiagnostics, qualification }

private structure runtimeCheckFields where
  kind : Option (String) := none
  enabled : Option (Bool) := none

private def runtimeCheck : Parser (Miri.MIR.RuntimeChecks × Bool) := do
  let fields ← object ({} : runtimeCheckFields) fun fields key => do
    match key with
    | "kind" => return { fields with kind := some (← string) }
    | "enabled" => return { fields with enabled := some (← boolean) }
    | _ => skipValue; pure fields
  let kind ← need fields.kind "kind"
  let enabled ← need fields.enabled "enabled"
  let check ← match kind with
    | "ub_checks" => pure Miri.MIR.RuntimeChecks.UbChecks
    | "contract_checks" => pure .ContractChecks
    | "overflow_checks" => pure .OverflowChecks
    | _ => fail "unknown compiler runtime-check kind"
  return (check, enabled)

private structure sessionFields where
  internalTargetFeatures : Option (Array (String)) := none
  isLikeWasm : Option (Bool) := none
  targetArch : Option (String) := none
  rootSpan : Option (Nat) := none
  runtimeChecks : Option (Array (Miri.MIR.RuntimeChecks × Bool)) := none

def session : Parser (Session) := do
  let fields ← object ({} : sessionFields) fun fields key => do
    match key with
    | "internal_target_features" => return { fields with internalTargetFeatures := some (← array (string)) }
    | "is_like_wasm" => return { fields with isLikeWasm := some (← boolean) }
    | "target_arch" => return { fields with targetArch := some (← string) }
    | "root_span" => return { fields with rootSpan := some (← natural) }
    | "runtime_checks" => return { fields with runtimeChecks := some (← array (runtimeCheck)) }
    | _ => skipValue; pure fields
  let internalTargetFeatures ← need fields.internalTargetFeatures "internal_target_features"
  let isLikeWasm ← need fields.isLikeWasm "is_like_wasm"
  let targetArch ← need fields.targetArch "target_arch"
  let rootSpan ← need fields.rootSpan "root_span"
  let runtimeChecks ← need fields.runtimeChecks "runtime_checks"
  let mut seen := #[]
  for (kind, _) in runtimeChecks do
    if seen.contains kind then fail "duplicate compiler runtime-check query"
    seen := seen.push kind
  return {
    internalTargetFeatures, isLikeWasm, targetArch, rootSpan, runtimeChecks }

private structure intrinsicFields where
  mustOverride : Option (Bool) := none
  fallbackIsSpec : Option (Bool) := none

private def intrinsic : Parser (IntrinsicMetadata) := do
  let fields ← object ({} : intrinsicFields) fun fields key => do
    match key with
    | "must_be_overridden" => return { fields with mustOverride := some (← boolean) }
    | "fallback_is_spec" => return { fields with fallbackIsSpec := some (← boolean) }
    | _ => skipValue; pure fields
  let mustOverride ← need fields.mustOverride "must_be_overridden"
  let fallbackIsSpec ← need fields.fallbackIsSpec "fallback_is_spec"
  return {
    mustOverride, fallbackIsSpec }

private structure targetFeatureFields where
  name : Option (String) := none
  kind : Option (String) := none

private def targetFeature : Parser (TargetFeature) := do
  let fields ← object ({} : targetFeatureFields) fun fields key => do
    match key with
    | "name" => return { fields with name := some (← string) }
    | "kind" => return { fields with kind := some (← string) }
    | _ => skipValue; pure fields
  let name ← need fields.name "name"
  let kind ← need fields.kind "kind"
  return {
    name, kind }

private structure runtimeInstanceFields where
  instanceId : Option (Nat) := none
  requiresCallerLocation : Option (Bool) := none
  display : Option (String) := none
  inlineNever : Option (Bool) := none
  targetFeatures : Option (Array (TargetFeature)) := none
  isForeignItem : Option (Bool) := none
  isClosureLike : Option (Bool) := none
  intrinsicMetadata : Option (Option IntrinsicMetadata) := none
  itemName : Option (String) := none
  codegenSymbolName : Option (Option String) := none
  symbolName : Option (String) := none

private def runtimeInstance : Parser (RuntimeInstance) := do
  let fields ← object ({} : runtimeInstanceFields) fun fields key => do
    match key with
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | "requires_caller_location" => return { fields with requiresCallerLocation := some (← boolean) }
    | "display" => return { fields with display := some (← string) }
    | "inline_never" => return { fields with inlineNever := some (← boolean) }
    | "target_features" => return { fields with targetFeatures := some (← array (targetFeature)) }
    | "is_foreign_item" => return { fields with isForeignItem := some (← boolean) }
    | "is_closure_like" => return { fields with isClosureLike := some (← boolean) }
    | "intrinsic_metadata" => return { fields with intrinsicMetadata := some (← nullable intrinsic) }
    | "item_name" => return { fields with itemName := some (← string) }
    | "codegen_symbol_name" => return { fields with codegenSymbolName := some (← nullable string) }
    | "symbol_name" => return { fields with symbolName := some (← string) }
    | _ => skipValue; pure fields
  let instanceId ← need fields.instanceId "instance_id"
  let requiresCallerLocation ← need fields.requiresCallerLocation "requires_caller_location"
  let display ← need fields.display "display"
  let inlineNever ← need fields.inlineNever "inline_never"
  let targetFeatures ← need fields.targetFeatures "target_features"
  let isForeignItem ← need fields.isForeignItem "is_foreign_item"
  let isClosureLike ← need fields.isClosureLike "is_closure_like"
  let intrinsicMetadata := fields.intrinsicMetadata
  let itemName := fields.itemName
  let codegenSymbolName := fields.codegenSymbolName
  let symbolName := fields.symbolName
  return {
    instanceId, requiresCallerLocation, display, inlineNever, targetFeatures, isForeignItem, isClosureLike, intrinsicMetadata, itemName, codegenSymbolName, symbolName }

private structure runtimeTypeFields where
  _environment : Option (String) := none
  inputType : Option (Nat) := none
  mutPointerType : Option (Nat) := none
  mutReferenceType : Option (Nat) := none
  dropGlue : Option (Nat) := none

private def runtimeType : Parser (RuntimeType) := do
  let fields ← object ({} : runtimeTypeFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "input_type_id" => return { fields with inputType := some (← natural) }
    | "mut_pointer_type" => return { fields with mutPointerType := some (← natural) }
    | "mut_reference_type" => return { fields with mutReferenceType := some (← natural) }
    | "drop_glue" => return { fields with dropGlue := some (← natural) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let inputType ← need fields.inputType "input_type_id"
  let mutPointerType ← need fields.mutPointerType "mut_pointer_type"
  let mutReferenceType ← need fields.mutReferenceType "mut_reference_type"
  let dropGlue := fields.dropGlue
  return {
    inputType, mutPointerType, mutReferenceType, dropGlue }

private structure vtableRefFields where
  inputType : Option (Nat) := none
  inputPredicates : Option (Array (Nat)) := none
  queryId : Option (Nat) := none

private def vtableRef : Parser (VtableRef) := do
  let fields ← object ({} : vtableRefFields) fun fields key => do
    match key with
    | "input_type" => return { fields with inputType := some (← natural) }
    | "input_predicates" => return { fields with inputPredicates := some (← array (natural)) }
    | "query_id" => return { fields with queryId := some (← natural) }
    | _ => skipValue; pure fields
  let inputType ← need fields.inputType "input_type"
  let inputPredicates ← need fields.inputPredicates "input_predicates"
  let queryId ← need fields.queryId "query_id"
  return {
    inputType, inputPredicates, queryId }

private structure runtimeVirtualFields where
  _environment : Option (String) := none
  originalInstance : Option (Nat) := none
  methodDefinition : Option (Nat) := none
  parentTrait : Option (Nat) := none
  concreteType : Option (Nat) := none
  rebasedArgs : Option (Array Miri.MIR.GenericArg) := none
  resolved : Option (Nat) := none
  vtableQuery : Option (VtableRef) := none

private def runtimeVirtual : Parser (RuntimeVirtual) := do
  let fields ← object ({} : runtimeVirtualFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "original_instance_id" => return { fields with originalInstance := some (← natural) }
    | "method_definition" => return { fields with methodDefinition := some (← natural) }
    | "parent_trait" => return { fields with parentTrait := some (← natural) }
    | "concrete_type" => return { fields with concreteType := some (← natural) }
    | "rebased_args" => return { fields with rebasedArgs := some (← GenericArgsCodec.decode) }
    | "resolved" => return { fields with resolved := some (← natural) }
    | "vtable_query" => return { fields with vtableQuery := some (← vtableRef) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let originalInstance ← need fields.originalInstance "original_instance_id"
  let methodDefinition ← need fields.methodDefinition "method_definition"
  let parentTrait ← need fields.parentTrait "parent_trait"
  let concreteType ← need fields.concreteType "concrete_type"
  let rebasedArgs ← need fields.rebasedArgs "rebased_args"
  let resolved ← need fields.resolved "resolved"
  let vtableQuery ← need fields.vtableQuery "vtable_query"
  return {
    originalInstance, methodDefinition, parentTrait, concreteType, rebasedArgs, resolved, vtableQuery }

private structure escapeDefaultFields where
  definition : Option (Nat) := none
  available : Option (Bool) := none

private def escapeDefault : Parser (DefinitionRef × Bool) := do
  let fields ← object ({} : escapeDefaultFields) fun fields key => do
    match key with
    | "definition" => return { fields with definition := some (← natural) }
    | "mir_available" => return { fields with available := some (← boolean) }
    | _ => skipValue; pure fields
  let definition ← need fields.definition "definition"
  let available ← need fields.available "mir_available"
  return (definition, available)

private structure startupFields where
  noCore : Option (Bool) := none
  coreEscapeDefault : Option (DefinitionRef × Bool) := none

private def startup : Parser (Startup) := do
  let fields ← object ({} : startupFields) fun fields key => do
    match key with
    | "no_core" => return { fields with noCore := some (← boolean) }
    | "core_escape_default" => return { fields with coreEscapeDefault := some (← escapeDefault) }
    | _ => skipValue; pure fields
  let noCore ← need fields.noCore "no_core"
  let coreEscapeDefault := fields.coreEscapeDefault
  return {
    noCore, coreEscapeDefault }

private structure linkageFields where
  kind : Option (String) := none
  raw : Option (String) := none

private def linkage : Parser (ImportLinkage) := do
  let fields ← object ({} : linkageFields) fun fields key => do
    match key with
    | "kind" => return { fields with kind := some (← string) }
    | "raw" => return { fields with raw := some (← string) }
    | _ => skipValue; pure fields
  let kind ← need fields.kind "kind"
  let raw := fields.raw
  match kind with
  | "none" =>
    if raw.isSome then fail "none import linkage carries raw payload"
    pure .none
  | "external_weak" => return .externalWeak (← need raw "raw")
  | "other" => return .other (← need raw "raw")
  | _ => fail "unknown extern import linkage"

private structure declarationFields where
  _environment : Option (String) := none
  definition : Option (Nat) := none
  symbol : Option (String) := none
  typeId : Option (Nat) := none
  layoutId : Option (Nat) := none
  importLinkage : Option (ImportLinkage) := none
  mutability : Option (String) := none
  typeIsFreeze : Option (Bool) := none
  declIsMut : Option (Bool) := none

private def declaration : Parser (ExternDeclaration) := do
  let fields ← object ({} : declarationFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "definition" => return { fields with definition := some (← natural) }
    | "symbol" => return { fields with symbol := some (← string) }
    | "type" => return { fields with typeId := some (← natural) }
    | "layout" => return { fields with layoutId := some (← natural) }
    | "import_linkage" => return { fields with importLinkage := some (← linkage) }
    | "definition_mutability" => return { fields with mutability := some (← string) }
    | "type_is_freeze" => return { fields with typeIsFreeze := some (← boolean) }
    | "decl_is_mut" => return { fields with declIsMut := some (← boolean) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let definition ← need fields.definition "definition"
  let symbol ← need fields.symbol "symbol"
  let typeId ← need fields.typeId "type"
  let layoutId ← need fields.layoutId "layout"
  let importLinkage ← need fields.importLinkage "import_linkage"
  let mutability ← need fields.mutability "definition_mutability"
  let typeIsFreeze ← need fields.typeIsFreeze "type_is_freeze"
  let declIsMut ← need fields.declIsMut "decl_is_mut"
  let definitionMutability ← match mutability with
    | "mutable" => pure MemoryMutability.mutable
    | "immutable" => pure .immutable
    | _ => fail "unknown extern definition mutability"
  return {
    definition, symbol, typeId, layoutId, importLinkage, definitionMutability, typeIsFreeze, declIsMut }

private structure candidateFields where
  iterationIndex : Option (Nat) := none
  used : Option (Bool) := none
  symbol : Option (String) := none
  definition : Option (Nat) := none
  explicitSymbol : Option (Bool) := none
  crateIndex : Option (Nat) := none
  crateName : Option (String) := none
  weak : Option (Bool) := none
  span : Option (Nat) := none
  definitionKind : Option (String) := none
  compilerBuiltins : Option (Bool) := none
  instanceId : Option (Nat) := none

private def candidate : Parser (ForeignCandidate) := do
  let fields ← object ({} : candidateFields) fun fields key => do
    match key with
    | "iteration_index" => return { fields with iterationIndex := some (← natural) }
    | "used" => return { fields with used := some (← boolean) }
    | "symbol" => return { fields with symbol := some (← string) }
    | "definition" => return { fields with definition := some (← natural) }
    | "explicit_symbol" => return { fields with explicitSymbol := some (← boolean) }
    | "crate_index" => return { fields with crateIndex := some (← natural) }
    | "crate_name" => return { fields with crateName := some (← string) }
    | "weak" => return { fields with weak := some (← boolean) }
    | "span" => return { fields with span := some (← natural) }
    | "definition_kind" => return { fields with definitionKind := some (← string) }
    | "compiler_builtins" => return { fields with compilerBuiltins := some (← boolean) }
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | _ => skipValue; pure fields
  let iterationIndex ← need fields.iterationIndex "iteration_index"
  let used ← need fields.used "used"
  let symbol ← need fields.symbol "symbol"
  let definition ← need fields.definition "definition"
  let explicitSymbol ← need fields.explicitSymbol "explicit_symbol"
  let crateIndex ← need fields.crateIndex "crate_index"
  let crateName ← need fields.crateName "crate_name"
  let weak ← need fields.weak "weak"
  let span ← need fields.span "span"
  let definitionKind ← need fields.definitionKind "definition_kind"
  let compilerBuiltins ← need fields.compilerBuiltins "compiler_builtins"
  let instanceId := fields.instanceId
  return {
    iterationIndex, used, symbol, definition, explicitSymbol, crateIndex, crateName, weak, span, definitionKind, compilerBuiltins, instanceId }

private structure selectedExportFields where
  symbol : Option (String) := none
  resolution : Option (String) := none
  reason : Option (String) := none
  kind : Option (String) := none
  definition : Option (Nat) := none
  declaration : Option (ExternDeclaration) := none
  allocation : Option (Nat) := none
  instanceId : Option (Option Nat) := none

private def selectedExport : Parser (SelectedExport) := do
  let fields ← object ({} : selectedExportFields) fun fields key => do
    match key with
    | "symbol" => return { fields with symbol := some (← string) }
    | "resolution" => return { fields with resolution := some (← string) }
    | "reason" => return { fields with reason := some (← string) }
    | "kind" => return { fields with kind := some (← string) }
    | "definition" => return { fields with definition := some (← natural) }
    | "declaration" => return { fields with declaration := some (← declaration) }
    | "allocation" => return { fields with allocation := some (← natural) }
    | "instance_id" => return { fields with instanceId := some (← nullable natural) }
    | _ => skipValue; pure fields
  let symbol ← need fields.symbol "symbol"
  let resolution := fields.resolution
  let reason := fields.reason
  let kind := fields.kind
  let definition := fields.definition
  let declaration := fields.declaration
  let allocation := fields.allocation
  let instanceId := fields.instanceId
  match resolution with
  | some "ambiguous" =>
    if kind.isSome || definition.isSome || declaration.isSome || allocation.isSome || instanceId.isSome then
      fail "ambiguous foreign export carries resolved payload"
    return .ambiguous symbol (← need reason "reason")
  | some _ => fail "unknown foreign export resolution"
  | none =>
    let kind ← need kind "kind"
    let definition ← need definition "definition"
    if reason.isSome then fail "resolved foreign export carries ambiguity reason"
    if kind == "static" then
      if instanceId.isSome then fail "static foreign export carries instance payload"
      return .static symbol definition (← need declaration "declaration") (← need allocation "allocation")
    if declaration.isSome || allocation.isSome then fail "non-static foreign export carries static payload"
    return .other symbol kind definition (← need instanceId "instance_id")

private structure fallbackFields where
  iterationIndex : Option (Nat) := none
  used : Option (Bool) := none
  symbol : Option (String) := none
  definition : Option (Nat) := none
  explicitSymbol : Option (Bool) := none
  crateIndex : Option (Nat) := none
  crateName : Option (String) := none
  weak : Option (Bool) := none
  span : Option (Nat) := none
  definitionKind : Option (String) := none
  compilerBuiltins : Option (Bool) := none
  instanceId : Option (Nat) := none
  resolution : Option (String) := none
  reason : Option (String) := none

private def fallback : Parser (ForeignFallback) := do
  let fields ← object ({} : fallbackFields) fun fields key => do
    match key with
    | "iteration_index" => return { fields with iterationIndex := some (← natural) }
    | "used" => return { fields with used := some (← boolean) }
    | "symbol" => return { fields with symbol := some (← string) }
    | "definition" => return { fields with definition := some (← natural) }
    | "explicit_symbol" => return { fields with explicitSymbol := some (← boolean) }
    | "crate_index" => return { fields with crateIndex := some (← natural) }
    | "crate_name" => return { fields with crateName := some (← string) }
    | "weak" => return { fields with weak := some (← boolean) }
    | "span" => return { fields with span := some (← natural) }
    | "definition_kind" => return { fields with definitionKind := some (← string) }
    | "compiler_builtins" => return { fields with compilerBuiltins := some (← boolean) }
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | "resolution" => return { fields with resolution := some (← string) }
    | "reason" => return { fields with reason := some (← string) }
    | _ => skipValue; pure fields
  let iterationIndex := fields.iterationIndex
  let used := fields.used
  let symbol := fields.symbol
  let definition := fields.definition
  let explicitSymbol := fields.explicitSymbol
  let crateIndex := fields.crateIndex
  let crateName := fields.crateName
  let weak := fields.weak
  let span := fields.span
  let definitionKind := fields.definitionKind
  let compilerBuiltins := fields.compilerBuiltins
  let instanceId := fields.instanceId
  let resolution := fields.resolution
  let reason := fields.reason
  match resolution with
  | some "ambiguous" =>
    if iterationIndex.isSome || used.isSome || definition.isSome || explicitSymbol.isSome ||
        crateIndex.isSome || crateName.isSome || weak.isSome || span.isSome ||
        definitionKind.isSome || compilerBuiltins.isSome || instanceId.isSome then
      fail "ambiguous foreign fallback carries candidate payload"
    return .ambiguous (← need symbol "symbol") (← need reason "reason")
  | some _ => fail "unknown foreign fallback resolution"
  | none =>
    if reason.isSome then fail "foreign candidate carries ambiguity reason"
    return .candidate {
    iterationIndex := ← need iterationIndex "iteration_index"
    used := ← need used "used"
    symbol := ← need symbol "symbol"
    definition := ← need definition "definition"
    explicitSymbol := ← need explicitSymbol "explicit_symbol"
    crateIndex := ← need crateIndex "crate_index"
    crateName := ← need crateName "crate_name"
    weak := ← need weak "weak"
    span := ← need span "span"
    definitionKind := ← need definitionKind "definition_kind"
    compilerBuiltins := ← need compilerBuiltins "compiler_builtins"
    instanceId := instanceId
  }

private structure allocatorTargetFields where
  kind : Option (String) := none
  method : Option (String) := none
  symbol : Option (String) := none

private def allocatorTarget : Parser (AllocatorTarget) := do
  let fields ← object ({} : allocatorTargetFields) fun fields key => do
    match key with
    | "kind" => return { fields with kind := some (← string) }
    | "method" => return { fields with method := some (← string) }
    | "symbol" => return { fields with symbol := some (← string) }
    | _ => skipValue; pure fields
  let kind ← need fields.kind "kind"
  let method := fields.method
  let symbol := fields.symbol
  match kind with
  | "special" =>
    if symbol.isSome then fail "special allocator target carries redirect symbol"
    return .special (← need method "method")
  | "redirect" =>
    if method.isSome then fail "redirect allocator target carries special method"
    return .redirect (← need symbol "symbol")
  | _ => fail "unknown allocator shim target"

private structure allocatorShimFields where
  symbol : Option (String) := none
  target : Option (AllocatorTarget) := none

private def allocatorShim : Parser (String × AllocatorTarget) := do
  let fields ← object ({} : allocatorShimFields) fun fields key => do
    match key with
    | "symbol" => return { fields with symbol := some (← string) }
    | "target" => return { fields with target := some (← allocatorTarget) }
    | _ => skipValue; pure fields
  let symbol ← need fields.symbol "symbol"
  let target ← need fields.target "target"
  return (symbol, target)

private structure foreignTargetFields where
  os : Option (String) := none
  env : Option (String) := none
  binaryFormat : Option (String) := none
  families : Option (Array (String)) := none

private def foreignTarget : Parser (String × String × String × Array String) := do
  let fields ← object ({} : foreignTargetFields) fun fields key => do
    match key with
    | "os" => return { fields with os := some (← string) }
    | "env" => return { fields with env := some (← string) }
    | "binary_format" => return { fields with binaryFormat := some (← string) }
    | "families" => return { fields with families := some (← array (string)) }
    | _ => skipValue; pure fields
  let os ← need fields.os "os"
  let env ← need fields.env "env"
  let binaryFormat ← need fields.binaryFormat "binary_format"
  let families ← need fields.families "families"
  return (os, env, binaryFormat, families)

private structure externStaticsFields where
  _environment : Option (String) := none
  declarations : Option (Array (ExternDeclaration)) := none
  exports : Option (Array (SelectedExport)) := none

private def externStatics : Parser (Array ExternDeclaration × Array SelectedExport) := do
  let fields ← object ({} : externStaticsFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "declarations" => return { fields with declarations := some (← array (declaration)) }
    | "selected_exported" => return { fields with exports := some (← array (selectedExport)) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let declarations ← need fields.declarations "declarations"
  let exports ← need fields.exports "selected_exported"
  return (declarations, exports)

private structure foreignSymbolsFields where
  target : Option (String × String × String × Array String) := none
  noAllocShimSymbol : Option (String) := none
  allocatorShims : Option (Array (String × AllocatorTarget)) := none
  exportedCandidates : Option (Array (ForeignCandidate)) := none
  selectedForeignFallbacks : Option (Array (ForeignFallback)) := none
  statics : Option (Array ExternDeclaration × Array SelectedExport) := none

private def foreignSymbols : Parser (ForeignSymbols) := do
  let fields ← object ({} : foreignSymbolsFields) fun fields key => do
    match key with
    | "target" => return { fields with target := some (← foreignTarget) }
    | "no_alloc_shim_symbol" => return { fields with noAllocShimSymbol := some (← string) }
    | "allocator_shims" => return { fields with allocatorShims := some (← array (allocatorShim)) }
    | "exported_candidates" => return { fields with exportedCandidates := some (← array (candidate)) }
    | "selected_foreign_fallbacks" => return { fields with selectedForeignFallbacks := some (← array (fallback)) }
    | "extern_statics" => return { fields with statics := some (← externStatics) }
    | _ => skipValue; pure fields
  let target ← need fields.target "target"
  let noAllocShimSymbol ← need fields.noAllocShimSymbol "no_alloc_shim_symbol"
  let allocatorShims ← need fields.allocatorShims "allocator_shims"
  let exportedCandidates := fields.exportedCandidates
  let selectedForeignFallbacks := fields.selectedForeignFallbacks
  let statics := fields.statics
  return {
    os := target.1, env := target.2.1, binaryFormat := target.2.2.1, families := target.2.2.2,
    noAllocShimSymbol, allocatorShims, exportedCandidates, selectedForeignFallbacks,
    externDeclarations := statics.map Prod.fst, selectedExports := statics.map Prod.snd }

private structure runtimeFields where
  startup : Option (Startup) := none
  types : Option (Array (RuntimeType)) := none
  virtualQueries : Option (Array (RuntimeVirtual)) := none
  instances : Option (Array (RuntimeInstance)) := none
  foreignSymbols : Option (ForeignSymbols) := none

def runtime : Parser (Runtime) := do
  let fields ← object ({} : runtimeFields) fun fields key => do
    match key with
    | "startup" => return { fields with startup := some (← startup) }
    | "types" => return { fields with types := some (← array (runtimeType)) }
    | "virtual" => return { fields with virtualQueries := some (← array (runtimeVirtual)) }
    | "instances" => return { fields with instances := some (← array (runtimeInstance)) }
    | "foreign_symbols" => return { fields with foreignSymbols := some (← foreignSymbols) }
    | _ => skipValue; pure fields
  let startup := fields.startup
  let types ← need fields.types "types"
  let virtualQueries ← need fields.virtualQueries "virtual"
  let instances ← need fields.instances "instances"
  let foreignSymbols ← need fields.foreignSymbols "foreign_symbols"
  return {
    startup, types, virtualQueries, instances, foreignSymbols }

private structure targetPointerFields where
  pointerSizeBytes : Option (Nat) := none
  pointerAlignBytes : Option (Nat) := none
  pointerOffsetBytes : Option (Nat) := none
  isFat : Option (Bool) := none

private def targetPointer : Parser (TargetPointerSpec) := do
  let fields ← object ({} : targetPointerFields) fun fields key => do
    match key with
    | "pointer_size_bytes" => return { fields with pointerSizeBytes := some (← natural) }
    | "pointer_align_bytes" => return { fields with pointerAlignBytes := some (← natural) }
    | "pointer_offset_bytes" => return { fields with pointerOffsetBytes := some (← natural) }
    | "is_fat" => return { fields with isFat := some (← boolean) }
    | _ => skipValue; pure fields
  let pointerSizeBytes ← need fields.pointerSizeBytes "pointer_size_bytes"
  let pointerAlignBytes ← need fields.pointerAlignBytes "pointer_align_bytes"
  let pointerOffsetBytes ← need fields.pointerOffsetBytes "pointer_offset_bytes"
  let isFat ← need fields.isFat "is_fat"
  return {
    pointerSizeBytes, pointerAlignBytes, pointerOffsetBytes, isFat }

private structure targetSpaceFields where
  addressSpace : Option (Nat) := none
  spec : Option (TargetPointerSpec) := none
  objectSizeBoundBytes : Option (Option Nat) := none

private def targetSpace : Parser (TargetAddressSpace) := do
  let fields ← object ({} : targetSpaceFields) fun fields key => do
    match key with
    | "address_space" => return { fields with addressSpace := some (← natural) }
    | "spec" => return { fields with spec := some (← targetPointer) }
    | "object_size_bound_bytes" => return { fields with objectSizeBoundBytes := some (← nullable natural) }
    | _ => skipValue; pure fields
  let addressSpace ← need fields.addressSpace "address_space"
  let spec ← need fields.spec "spec"
  let objectSizeBoundBytes ← need fields.objectSizeBoundBytes "object_size_bound_bytes"
  return {
    addressSpace, spec, objectSizeBoundBytes }

private structure vectorAlignFields where
  sizeBytes : Option (Nat) := none
  alignBytes : Option (Nat) := none

private def vectorAlign : Parser (Nat × Nat) := do
  let fields ← object ({} : vectorAlignFields) fun fields key => do
    match key with
    | "size_bytes" => return { fields with sizeBytes := some (← natural) }
    | "align_bytes" => return { fields with alignBytes := some (← natural) }
    | _ => skipValue; pure fields
  let sizeBytes ← need fields.sizeBytes "size_bytes"
  let alignBytes ← need fields.alignBytes "align_bytes"
  return (sizeBytes, alignBytes)

private structure targetDataLayoutFields where
  evidencePath : Option (String) := none
  llvmDataLayout : Option (String) := none
  privateInventoryEvidence : Option (String) := none
  alignmentEvidence : Option (String) := none
  endian : Option (String) := none
  pointerWidthBits : Option (Nat) := none
  objectSizeBoundBytes : Option (Option Nat) := none
  i1AlignBytes : Option (Nat) := none
  i8AlignBytes : Option (Nat) := none
  i16AlignBytes : Option (Nat) := none
  i32AlignBytes : Option (Nat) := none
  i64AlignBytes : Option (Nat) := none
  i128AlignBytes : Option (Nat) := none
  f16AlignBytes : Option (Nat) := none
  f32AlignBytes : Option (Nat) := none
  f64AlignBytes : Option (Nat) := none
  f128AlignBytes : Option (Nat) := none
  aggregateAlignBytes : Option (Nat) := none
  vectorAlign : Option (Array (Nat × Nat)) := none
  defaultAddressSpace : Option (Nat) := none
  defaultAddressSpacePointerSpec : Option (TargetPointerSpec) := none
  addressSpaceInfo : Option (Array (TargetAddressSpace)) := none
  instructionAddressSpace : Option (Nat) := none
  cEnumMinSize : Option (String) := none

def targetDataLayout : Parser (TargetDataLayoutEvidence) := do
  let fields ← object ({} : targetDataLayoutFields) fun fields key => do
    match key with
    | "evidence_path" => return { fields with evidencePath := some (← string) }
    | "llvm_data_layout" => return { fields with llvmDataLayout := some (← string) }
    | "private_inventory_evidence" => return { fields with privateInventoryEvidence := some (← string) }
    | "alignment_evidence" => return { fields with alignmentEvidence := some (← string) }
    | "endian" => return { fields with endian := some (← string) }
    | "pointer_width_bits" => return { fields with pointerWidthBits := some (← natural) }
    | "object_size_bound_bytes" => return { fields with objectSizeBoundBytes := some (← nullable natural) }
    | "i1_align_bytes" => return { fields with i1AlignBytes := some (← natural) }
    | "i8_align_bytes" => return { fields with i8AlignBytes := some (← natural) }
    | "i16_align_bytes" => return { fields with i16AlignBytes := some (← natural) }
    | "i32_align_bytes" => return { fields with i32AlignBytes := some (← natural) }
    | "i64_align_bytes" => return { fields with i64AlignBytes := some (← natural) }
    | "i128_align_bytes" => return { fields with i128AlignBytes := some (← natural) }
    | "f16_align_bytes" => return { fields with f16AlignBytes := some (← natural) }
    | "f32_align_bytes" => return { fields with f32AlignBytes := some (← natural) }
    | "f64_align_bytes" => return { fields with f64AlignBytes := some (← natural) }
    | "f128_align_bytes" => return { fields with f128AlignBytes := some (← natural) }
    | "aggregate_align_bytes" => return { fields with aggregateAlignBytes := some (← natural) }
    | "vector_align" => return { fields with vectorAlign := some (← array (vectorAlign)) }
    | "default_address_space" => return { fields with defaultAddressSpace := some (← natural) }
    | "default_address_space_pointer_spec" => return { fields with defaultAddressSpacePointerSpec := some (← targetPointer) }
    | "address_space_info" => return { fields with addressSpaceInfo := some (← array (targetSpace)) }
    | "instruction_address_space" => return { fields with instructionAddressSpace := some (← natural) }
    | "c_enum_min_size" => return { fields with cEnumMinSize := some (← string) }
    | _ => skipValue; pure fields
  let evidencePath ← need fields.evidencePath "evidence_path"
  let llvmDataLayout ← need fields.llvmDataLayout "llvm_data_layout"
  let privateInventoryEvidence ← need fields.privateInventoryEvidence "private_inventory_evidence"
  let alignmentEvidence ← need fields.alignmentEvidence "alignment_evidence"
  let endian ← need fields.endian "endian"
  let pointerWidthBits ← need fields.pointerWidthBits "pointer_width_bits"
  let objectSizeBoundBytes ← need fields.objectSizeBoundBytes "object_size_bound_bytes"
  let i1AlignBytes ← need fields.i1AlignBytes "i1_align_bytes"
  let i8AlignBytes ← need fields.i8AlignBytes "i8_align_bytes"
  let i16AlignBytes ← need fields.i16AlignBytes "i16_align_bytes"
  let i32AlignBytes ← need fields.i32AlignBytes "i32_align_bytes"
  let i64AlignBytes ← need fields.i64AlignBytes "i64_align_bytes"
  let i128AlignBytes ← need fields.i128AlignBytes "i128_align_bytes"
  let f16AlignBytes ← need fields.f16AlignBytes "f16_align_bytes"
  let f32AlignBytes ← need fields.f32AlignBytes "f32_align_bytes"
  let f64AlignBytes ← need fields.f64AlignBytes "f64_align_bytes"
  let f128AlignBytes ← need fields.f128AlignBytes "f128_align_bytes"
  let aggregateAlignBytes ← need fields.aggregateAlignBytes "aggregate_align_bytes"
  let vectorAlign ← need fields.vectorAlign "vector_align"
  let defaultAddressSpace ← need fields.defaultAddressSpace "default_address_space"
  let defaultAddressSpacePointerSpec ← need fields.defaultAddressSpacePointerSpec "default_address_space_pointer_spec"
  let addressSpaceInfo ← need fields.addressSpaceInfo "address_space_info"
  let instructionAddressSpace ← need fields.instructionAddressSpace "instruction_address_space"
  let cEnumMinSize ← need fields.cEnumMinSize "c_enum_min_size"
  return {
    evidencePath, llvmDataLayout, privateInventoryEvidence, alignmentEvidence, endian, pointerWidthBits, objectSizeBoundBytes, i1AlignBytes, i8AlignBytes, i16AlignBytes, i32AlignBytes, i64AlignBytes, i128AlignBytes, f16AlignBytes, f32AlignBytes, f64AlignBytes, f128AlignBytes, aggregateAlignBytes, vectorAlign, defaultAddressSpace, defaultAddressSpacePointerSpec, addressSpaceInfo, instructionAddressSpace, cEnumMinSize }

end Miri.Input.CatalogDecoder
