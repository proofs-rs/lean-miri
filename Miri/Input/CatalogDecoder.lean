import Miri.Input.Model.Catalogs
import Miri.Input.JsonReader
import Miri.Input.GenericArgsCodec
import Miri.Input.DecoderValues
import Miri.Input.DecodeMIR
import Miri.Input.CatalogDecoderRuntime

/- Catalog objects are parsed once into schema-specific accumulators. Only
constants need draft values: their scalar widths are resolved against completed
type/layout tables, just like constants inside MIR bodies. -/
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

private def signature : Parser Signature := do
  let value ← DecoderValues.parseFunctionSignature "$signature"
  pure {
    inputs := value.inputs, output := value.output, safety := value.safety,
    abi := value.abi, cVariadic := value.cVariadic }

private structure crateRowFields where
  crate : Option (Nat) := none
  name : Option (String) := none

private def crateRow : Parser (Nat × String) := do
  let fields ← object ({} : crateRowFields) fun fields key => do
    match key with
    | "crate" => return { fields with crate := some (← natural) }
    | "name" => return { fields with name := some (← string) }
    | _ => skipValue; pure fields
  let crate ← need fields.crate "crate"
  let name ← need fields.name "name"
  return (crate, name)

private structure frame_metadataFields where
  localCrate : Option (Nat) := none
  crates : Option (Array (Nat × String)) := none

def frame_metadata : Parser (FrameMetadata) := do
  let fields ← object ({} : frame_metadataFields) fun fields key => do
    match key with
    | "local_crate" => return { fields with localCrate := some (← natural) }
    | "crates" => return { fields with crates := some (← array (crateRow)) }
    | _ => skipValue; pure fields
  let localCrate ← need fields.localCrate "local_crate"
  let crates ← need fields.crates "crates"
  return {
    localCrate, crates }

private structure instance_abiFields where
  _environment : Option (String) := none
  instanceId : Option (Nat) := none
  extraArgumentTypes : Option (Array (Nat)) := none
  abiId : Option (Nat) := none

def instance_abi : Parser (InstanceAbi) := do
  let fields ← object ({} : instance_abiFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | "extra_argument_types" => return { fields with extraArgumentTypes := some (← array (natural)) }
    | "abi_query" => return { fields with abiId := some (← natural) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let instanceId ← need fields.instanceId "instance_id"
  let extraArgumentTypes ← need fields.extraArgumentTypes "extra_argument_types"
  let abiId ← need fields.abiId "abi_query"
  return {
    instanceId, extraArgumentTypes, abiId }

private structure pointer_abiFields where
  _environment : Option (String) := none
  typeId : Option (Nat) := none
  extraArgumentTypes : Option (Array (Nat)) := none
  abiId : Option (Nat) := none

def pointer_abi : Parser (PointerAbi) := do
  let fields ← object ({} : pointer_abiFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "type_id" => return { fields with typeId := some (← natural) }
    | "extra_argument_types" => return { fields with extraArgumentTypes := some (← array (natural)) }
    | "abi_query" => return { fields with abiId := some (← natural) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let typeId ← need fields.typeId "type_id"
  let extraArgumentTypes ← need fields.extraArgumentTypes "extra_argument_types"
  let abiId ← need fields.abiId "abi_query"
  return {
    typeId, extraArgumentTypes, abiId }

private structure helper_signatureFields where
  _environment : Option (String) := none
  signature : Option (Signature) := none
  splatted : Option (Bool) := none
  abiId : Option (Nat) := none

def helper_signature : Parser (HelperSignature) := do
  let fields ← object ({} : helper_signatureFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "signature" => return { fields with signature := some (← signature) }
    | "splatted" => return { fields with splatted := some (← boolean) }
    | "abi_query" => return { fields with abiId := some (← natural) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let signature ← need fields.signature "signature"
  let splatted ← need fields.splatted "splatted"
  let abiId ← need fields.abiId "abi_query"
  return {
    signature, splatted, abiId }

private structure native_signatureFields where
  instanceId : Option (Nat) := none
  query : Option (String) := none
  normalization : Option (String) := none
  boundRegions : Option (String) := none
  signature : Option (Signature) := none

def native_signature : Parser (NativeSignature) := do
  let fields ← object ({} : native_signatureFields) fun fields key => do
    match key with
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | "query" => return { fields with query := some (← string) }
    | "normalization" => return { fields with normalization := some (← string) }
    | "bound_regions" => return { fields with boundRegions := some (← string) }
    | "signature_query" => return { fields with signature := some (← signature) }
    | _ => skipValue; pure fields
  let instanceId ← need fields.instanceId "instance_id"
  let query ← need fields.query "query"
  let normalization ← need fields.normalization "normalization"
  let boundRegions ← need fields.boundRegions "bound_regions"
  let signature ← need fields.signature "signature_query"
  return {
    instanceId, query, normalization, boundRegions, signature }

private structure retag_queryFields where
  definition : Option (Nat) := none
  rustcNoWritable : Option (Bool) := none

def retag_query : Parser (RetagQuery) := do
  let fields ← object ({} : retag_queryFields) fun fields key => do
    match key with
    | "definition" => return { fields with definition := some (← natural) }
    | "rustc_no_writable" => return { fields with rustcNoWritable := some (← boolean) }
    | _ => skipValue; pure fields
  let definition ← need fields.definition "definition"
  let rustcNoWritable ← need fields.rustcNoWritable "rustc_no_writable"
  return {
    definition, rustcNoWritable }

private structure covarianceFields where
  _environment : Option (String) := none
  sourceType : Option (Nat) := none
  targetType : Option (Nat) := none
  value : Option (Bool) := none
  _variance : Option (String) := none

private def covariance : Parser (CovarianceQuery) := do
  let fields ← object ({} : covarianceFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "source_type" => return { fields with sourceType := some (← natural) }
    | "target_type" => return { fields with targetType := some (← natural) }
    | "value" => return { fields with value := some (← boolean) }
    | "variance" => return { fields with _variance := some (← expectedString "covariant") }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let sourceType ← need fields.sourceType "source_type"
  let targetType ← need fields.targetType "target_type"
  let value ← need fields.value "value"
  let _variance ← need fields._variance "variance"
  return {
    sourceType, targetType, value }

private structure start_resolutionFields where
  instanceId : Option (Nat) := none
  functionType : Option (Nat) := none

private def start_resolution : Parser (StartResolution) := do
  let fields ← object ({} : start_resolutionFields) fun fields key => do
    match key with
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | "function_type" => return { fields with functionType := some (← natural) }
    | _ => skipValue; pure fields
  let instanceId ← need fields.instanceId "instance_id"
  let functionType ← need fields.functionType "function_type"
  return {
    instanceId, functionType }

private structure entry_signatureFields where
  compilerSelectedEntry : Option (Bool) := none
  hasBoundVariables : Option (Bool) := none
  outputHasBoundVariables : Option (Bool) := none
  returnType : Option (Nat) := none
  functionPointerType : Option (Nat) := none
  startResolution : Option (Option StartResolution) := none

private def entry_signature : Parser (EntrySignature) := do
  let fields ← object ({} : entry_signatureFields) fun fields key => do
    match key with
    | "compiler_selected_entry" => return { fields with compilerSelectedEntry := some (← boolean) }
    | "has_bound_variables" => return { fields with hasBoundVariables := some (← boolean) }
    | "output_has_bound_variables" => return { fields with outputHasBoundVariables := some (← boolean) }
    | "return_type" => return { fields with returnType := some (← natural) }
    | "function_pointer_type" => return { fields with functionPointerType := some (← natural) }
    | "start_resolution" => return { fields with startResolution := some (← nullable start_resolution) }
    | _ => skipValue; pure fields
  let compilerSelectedEntry ← need fields.compilerSelectedEntry "compiler_selected_entry"
  let hasBoundVariables ← need fields.hasBoundVariables "has_bound_variables"
  let outputHasBoundVariables ← need fields.outputHasBoundVariables "output_has_bound_variables"
  let returnType ← need fields.returnType "return_type"
  let functionPointerType ← need fields.functionPointerType "function_pointer_type"
  let startResolution ← need fields.startResolution "start_resolution"
  return {
    compilerSelectedEntry, hasBoundVariables, outputHasBoundVariables, returnType, functionPointerType, startResolution }

private structure main_entryFields where
  definition : Option (Nat) := none
  genericParameters : Option (Array (String)) := none
  signature : Option (EntrySignature) := none

private def main_entry : Parser (MainEntry) := do
  let fields ← object ({} : main_entryFields) fun fields key => do
    match key with
    | "definition" => return { fields with definition := some (← natural) }
    | "generic_parameters" => return { fields with genericParameters := some (← array (string)) }
    | "signature_query" => return { fields with signature := some (← entry_signature) }
    | _ => skipValue; pure fields
  let definition ← need fields.definition "definition"
  let genericParameters ← need fields.genericParameters "generic_parameters"
  let signature ← need fields.signature "signature_query"
  return {
    definition, genericParameters, signature }

private structure compiler_entryFields where
  definition : Option (Nat) := none
  kind : Option (String) := none
  sigpipe : Option (Nat) := none

private def compiler_entry : Parser (CompilerEntry) := do
  let fields ← object ({} : compiler_entryFields) fun fields key => do
    match key with
    | "definition" => return { fields with definition := some (← natural) }
    | "kind" => return { fields with kind := some (← string) }
    | "sigpipe" => return { fields with sigpipe := some (← natural) }
    | _ => skipValue; pure fields
  let definition ← need fields.definition "definition"
  let kind ← need fields.kind "kind"
  let sigpipe ← need fields.sigpipe "sigpipe"
  return {
    definition, kind, sigpipe }

private structure primitivesFields where
  u8 : Option (Nat) := none
  u16 : Option (Nat) := none
  u32 : Option (Nat) := none
  u64 : Option (Nat) := none
  u128 : Option (Nat) := none
  i8 : Option (Nat) := none
  i16 : Option (Nat) := none
  i32 : Option (Nat) := none
  i64 : Option (Nat) := none
  i128 : Option (Nat) := none
  bool : Option (Nat) := none
  pointerTagInteger : Option (Nat) := none
  usize : Option (Nat) := none
  isize : Option (Nat) := none
  unit : Option (Nat) := none
  unitPointerConst : Option (Nat) := none
  unitPointerMut : Option (Nat) := none
  immU8Pointer : Option (Nat) := none
  immU8PointerPointer : Option (Nat) := none
  callerLocationType : Option (Option Nat) := none
  orderingEnum : Option (Option Nat) := none

def primitives : Parser (Primitives) := do
  let fields ← object ({} : primitivesFields) fun fields key => do
    match key with
    | "u8" => return { fields with u8 := some (← natural) }
    | "u16" => return { fields with u16 := some (← natural) }
    | "u32" => return { fields with u32 := some (← natural) }
    | "u64" => return { fields with u64 := some (← natural) }
    | "u128" => return { fields with u128 := some (← natural) }
    | "i8" => return { fields with i8 := some (← natural) }
    | "i16" => return { fields with i16 := some (← natural) }
    | "i32" => return { fields with i32 := some (← natural) }
    | "i64" => return { fields with i64 := some (← natural) }
    | "i128" => return { fields with i128 := some (← natural) }
    | "bool" => return { fields with bool := some (← natural) }
    | "pointer_tag_integer" => return { fields with pointerTagInteger := some (← natural) }
    | "usize" => return { fields with usize := some (← natural) }
    | "isize" => return { fields with isize := some (← natural) }
    | "unit" => return { fields with unit := some (← natural) }
    | "unit_pointer_const" => return { fields with unitPointerConst := some (← natural) }
    | "unit_pointer_mut" => return { fields with unitPointerMut := some (← natural) }
    | "imm_u8_pointer" => return { fields with immU8Pointer := some (← natural) }
    | "imm_u8_pointer_pointer" => return { fields with immU8PointerPointer := some (← natural) }
    | "caller_location_type" => return { fields with callerLocationType := some (← nullable natural) }
    | "ordering_enum" => return { fields with orderingEnum := some (← nullable natural) }
    | _ => skipValue; pure fields
  let u8 ← need fields.u8 "u8"
  let u16 ← need fields.u16 "u16"
  let u32 ← need fields.u32 "u32"
  let u64 ← need fields.u64 "u64"
  let u128 ← need fields.u128 "u128"
  let i8 ← need fields.i8 "i8"
  let i16 ← need fields.i16 "i16"
  let i32 ← need fields.i32 "i32"
  let i64 ← need fields.i64 "i64"
  let i128 ← need fields.i128 "i128"
  let bool ← need fields.bool "bool"
  let pointerTagInteger ← need fields.pointerTagInteger "pointer_tag_integer"
  let usize ← need fields.usize "usize"
  let isize ← need fields.isize "isize"
  let unit ← need fields.unit "unit"
  let unitPointerConst ← need fields.unitPointerConst "unit_pointer_const"
  let unitPointerMut ← need fields.unitPointerMut "unit_pointer_mut"
  let immU8Pointer ← need fields.immU8Pointer "imm_u8_pointer"
  let immU8PointerPointer ← need fields.immU8PointerPointer "imm_u8_pointer_pointer"
  let callerLocationType := fields.callerLocationType
  let orderingEnum := fields.orderingEnum
  return {
    u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, bool, pointerTagInteger, usize, isize, unit, unitPointerConst, unitPointerMut, immU8Pointer, immU8PointerPointer, callerLocationType := callerLocationType.join, orderingEnum := orderingEnum.join }

private structure shim_signatureFields where
  callingConvention : Option (String) := none
  arguments : Option (Array (String)) := none
  result : Option (String) := none
  cVariadic : Option (Bool) := none

private def shim_signature : Parser (ShimSignature) := do
  let fields ← object ({} : shim_signatureFields) fun fields key => do
    match key with
    | "calling_convention" => return { fields with callingConvention := some (← string) }
    | "arguments" => return { fields with arguments := some (← array (string)) }
    | "return" => return { fields with result := some (← string) }
    | "c_variadic" => return { fields with cVariadic := some (← boolean) }
    | _ => skipValue; pure fields
  let callingConvention ← need fields.callingConvention "calling_convention"
  let arguments ← need fields.arguments "arguments"
  let result ← need fields.result "return"
  let cVariadic ← need fields.cVariadic "c_variadic"
  return {
    callingConvention, arguments, result, cVariadic }

private structure functionKindFields where
  kind : Option (String) := none
  instanceId : Option (Nat) := none

private def functionKind : Parser (Option Nat) := do
  let fields ← object ({} : functionKindFields) fun fields key => do
    match key with
    | "kind" => return { fields with kind := some (← string) }
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | _ => skipValue; pure fields
  let kind ← need fields.kind "kind"
  let instanceId := fields.instanceId
  match kind with
  | "function_pointer" =>
    if instanceId.isSome then fail "function pointer kind carries instance"
    pure none
  | "function_definition" => some <$> need instanceId "instance_id"
  | _ => fail "unknown compiler function kind"

private structure functionTypeFields where
  _environment : Option (String) := none
  typeId : Option (Nat) := none
  instanceId : Option (Option Nat) := none
  signature : Option (Signature) := none

private def functionType : Parser (FunctionType) := do
  let fields ← object ({} : functionTypeFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "type_id" => return { fields with typeId := some (← natural) }
    | "function_kind" => return { fields with instanceId := some (← functionKind) }
    | "signature_query" => return { fields with signature := some (← signature) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let typeId ← need fields.typeId "type_id"
  let instanceId ← need fields.instanceId "function_kind"
  let signature ← need fields.signature "signature_query"
  return {
    typeId, instanceId, signature }

private structure functionFactsFields where
  types : Option (Array (FunctionType)) := none
  pointerAbis : Option (Array (PointerAbi)) := none
  helperSignatures : Option (Array (HelperSignature)) := none

def functionFacts : Parser (FunctionFacts) := do
  let fields ← object ({} : functionFactsFields) fun fields key => do
    match key with
    | "types" => return { fields with types := some (← array (functionType)) }
    | "pointer_abis" => return { fields with pointerAbis := some (← array (pointer_abi)) }
    | "helper_signatures" => return { fields with helperSignatures := some (← array (helper_signature)) }
    | _ => skipValue; pure fields
  let types ← need fields.types "types"
  let pointerAbis ← need fields.pointerAbis "pointer_abis"
  let helperSignatures ← need fields.helperSignatures "helper_signatures"
  return {
    types, pointerAbis, helperSignatures }

private structure castQueryFields where
  _environment : Option (String) := none
  kind : Option (String) := none
  resolution : Option (String) := none
  resolvedInstance : Option (Nat) := none
  input : Option (Nat) := none
  args : Option (Bool) := none
  source : Option (Nat) := none
  target : Option (Nat) := none
  value : Option (Option Nat) := none
  sourceTail : Option (Nat) := none
  targetTail : Option (Nat) := none
  output : Option (Nat) := none

def castQuery : Parser (CastQuery) := do
  let fields ← object ({} : castQueryFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "query_kind" => return { fields with kind := some (← string) }
    | "resolution_kind" => return { fields with resolution := some (← string) }
    | "instance_id" => return { fields with resolvedInstance := some (← natural) }
    | "input_type" => return { fields with input := some (← natural) }
    | "args_no_bound_vars" => return { fields with args := some (← boolean) }
    | "input_source" => return { fields with source := some (← natural) }
    | "input_target" => return { fields with target := some (← natural) }
    | "value" =>
      if (← Std.Internal.Parsec.peek!) == '{' then
        fail "obsolete wrapped compiler cast query value"
      return { fields with value := some (← nullable natural) }
    | "source_tail" => return { fields with sourceTail := some (← natural) }
    | "target_tail" => return { fields with targetTail := some (← natural) }
    | "type" => return { fields with output := some (← natural) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let kind ← need fields.kind "query_kind"
  let resolution := fields.resolution
  let resolvedInstance := fields.resolvedInstance
  let input := fields.input
  let args := fields.args
  let source := fields.source
  let target := fields.target
  let value := fields.value
  let sourceTail := fields.sourceTail
  let targetTail := fields.targetTail
  let output := fields.output
  let hasUnary := input.isSome || args.isSome || resolvedInstance.isSome || resolution.isSome
  let hasPair := source.isSome || target.isSome
  let hasTails := sourceTail.isSome || targetTail.isSome
  match kind with
  | "resolve_fn_ptr" | "resolve_closure_fn_once" =>
    if hasPair || hasTails || value.isSome || output.isSome then
      fail "function resolution carries unrelated query payload"
    if kind == "resolve_closure_fn_once" && resolution.isSome then
      fail "closure resolution carries function resolution kind"
  | "supertrait_slot" =>
    if hasUnary || hasTails || output.isSome then fail "supertrait slot carries unrelated query payload"
  | "lockstep_tails" =>
    if hasUnary || value.isSome || output.isSome then fail "lockstep tails carries unrelated query payload"
  | "box_type" =>
    if args.isSome || resolvedInstance.isSome || resolution.isSome || hasPair || hasTails || value.isSome then
      fail "box type carries unrelated query payload"
  | _ => pure ()
  match kind with
  | "resolve_fn_ptr" =>
    let resolved ← match ← need resolution "resolution_kind" with
      | "none" =>
        if resolvedInstance.isSome then fail "absent function resolution carries instance"
        pure none
      | "instance" => some <$> need resolvedInstance "instance_id"
      | _ => fail "unknown function resolution kind"
    return .resolveFnPtr (← need input "input_type") (← need args "args_no_bound_vars") resolved
  | "resolve_closure_fn_once" => return .resolveClosureFnOnce (← need input "input_type") (← need args "args_no_bound_vars") (← need resolvedInstance "instance_id")
  | "supertrait_slot" => return .supertraitSlot (← need source "input_source") (← need target "input_target") (← need value "value")
  | "lockstep_tails" => return .lockstepTails (← need source "input_source") (← need target "input_target") (← need sourceTail "source_tail") (← need targetTail "target_tail")
  | "box_type" => return .boxType (← need input "input_type") (← need output "type")
  | _ => fail "unknown compiler cast query"

private structure panicQueryFields where
  langItem : Option (String) := none
  definition : Option (Option Nat) := none
  genericParameters : Option (Option (Array String)) := none

def panicQuery : Parser (PanicQuery) := do
  let fields ← object ({} : panicQueryFields) fun fields key => do
    match key with
    | "lang_item" => return { fields with langItem := some (← string) }
    | "definition" => return { fields with definition := some (← nullable natural) }
    | "generic_parameters" => return { fields with genericParameters := some (← nullable (array string)) }
    | _ => skipValue; pure fields
  let langItem ← need fields.langItem "lang_item"
  let definition ← need fields.definition "definition"
  let genericParameters := fields.genericParameters
  return {
    langItem, definition, genericParameters := genericParameters.join }

private structure saltRowFields where
  salt : Option (Nat) := none
  existing : Option (Option Nat) := none

private def saltRow : Parser (Nat × Option Nat) := do
  let fields ← object ({} : saltRowFields) fun fields key => do
    match key with
    | "salt" => return { fields with salt := some (← natural) }
    | "existing_allocation" => return { fields with existing := some (← nullable natural) }
    | _ => skipValue; pure fields
  let salt ← need fields.salt "salt"
  let existing ← need fields.existing "existing_allocation"
  return (salt, existing)

private structure byteCandidateFields where
  bytesHex : Option (String) := none
  salts : Option (Array (Nat × Option Nat)) := none

private def byteCandidate : Parser (GlobalByteCandidate) := do
  let fields ← object ({} : byteCandidateFields) fun fields key => do
    match key with
    | "bytes_hex" => return { fields with bytesHex := some (← string) }
    | "salts" => return { fields with salts := some (← array (saltRow)) }
    | _ => skipValue; pure fields
  let bytesHex ← need fields.bytesHex "bytes_hex"
  let salts ← need fields.salts "salts"
  return {
    bytesHex, salts }

private structure globalBytesFields where
  saltCount : Option (Nat) := none
  strType : Option (Nat) := none
  coveredAllocations : Option (Array (Nat)) := none
  candidates : Option (Array (GlobalByteCandidate)) := none

def globalBytes : Parser (GlobalBytes) := do
  let fields ← object ({} : globalBytesFields) fun fields key => do
    match key with
    | "salt_count" => return { fields with saltCount := some (← natural) }
    | "str_type" => return { fields with strType := some (← natural) }
    | "covered_allocation_ids" => return { fields with coveredAllocations := some (← array (natural)) }
    | "candidates" => return { fields with candidates := some (← array (byteCandidate)) }
    | _ => skipValue; pure fields
  let saltCount ← need fields.saltCount "salt_count"
  let strType ← need fields.strType "str_type"
  let coveredAllocations ← need fields.coveredAllocations "covered_allocation_ids"
  let candidates ← need fields.candidates "candidates"
  return {
    saltCount, strType, coveredAllocations, candidates }

private structure globalQueryFields where
  typeId : Option (Nat) := none
  allocation : Option (Nat) := none

private def globalQuery : Parser (Nat × Nat) := do
  let fields ← object ({} : globalQueryFields) fun fields key => do
    match key with
    | "type" => return { fields with typeId := some (← natural) }
    | "allocation" => return { fields with allocation := some (← natural) }
    | _ => skipValue; pure fields
  let typeId ← need fields.typeId "type"
  let allocation ← need fields.allocation "allocation"
  return (typeId, allocation)

private structure linkSectionFields where
  sectionName : Option (String) := none
  definition : Option (Nat) := none
  span : Option (Nat) := none
  query : Option (Nat × Nat) := none

private def linkSection : Parser (LinkSection) := do
  let fields ← object ({} : linkSectionFields) fun fields key => do
    match key with
    | "section" => return { fields with sectionName := some (← string) }
    | "definition" => return { fields with definition := some (← natural) }
    | "span" => return { fields with span := some (← natural) }
    | "global_query" => return { fields with query := some (← globalQuery) }
    | _ => skipValue; pure fields
  let sectionName ← need fields.sectionName "section"
  let definition ← need fields.definition "definition"
  let span ← need fields.span "span"
  let query ← need fields.query "global_query"
  return {
    sectionName, definition, span, typeId := query.1, allocation := query.2 }

private structure mainQueriesFields where
  _environment : Option (String) := none
  startLangItem : Option (Option Nat) := none
  compilerEntry : Option (Option Nat) := none
  compilerEntryType : Option (Option CompilerEntry) := none
  entries : Option (Array (MainEntry)) := none
  linkSections : Option (Option (Array LinkSection)) := none

def mainQueries : Parser (Main) := do
  let fields ← object ({} : mainQueriesFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "start_lang_item" => return { fields with startLangItem := some (← nullable natural) }
    | "compiler_entry" => return { fields with compilerEntry := some (← nullable natural) }
    | "compiler_entry_type" => return { fields with compilerEntryType := some (← nullable compiler_entry) }
    | "entries" => return { fields with entries := some (← array (main_entry)) }
    | "link_sections" => return { fields with linkSections := some (← nullable (array linkSection)) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let startLangItem ← need fields.startLangItem "start_lang_item"
  let compilerEntry ← need fields.compilerEntry "compiler_entry"
  let compilerEntryType ← need fields.compilerEntryType "compiler_entry_type"
  let entries ← need fields.entries "entries"
  let linkSections := fields.linkSections
  return {
    startLangItem, compilerEntry, compilerEntryType, entries, linkSections := linkSections.join }

private structure shimQueryFields where
  inputs : Option (Array (Nat)) := none
  output : Option (Nat) := none
  abi : Option (Nat) := none

private def shimQuery : Parser (Array Nat × Nat × Nat) := do
  let fields ← object ({} : shimQueryFields) fun fields key => do
    match key with
    | "input_types" => return { fields with inputs := some (← array (natural)) }
    | "output_type" => return { fields with output := some (← natural) }
    | "abi_query" => return { fields with abi := some (← natural) }
    | _ => skipValue; pure fields
  let inputs ← need fields.inputs "input_types"
  let output ← need fields.output "output_type"
  let abi ← need fields.abi "abi_query"
  return (inputs, output, abi)

private structure shimAbiFields where
  _environment : Option (String) := none
  signature : Option (ShimSignature) := none
  query : Option (Array Nat × Nat × Nat) := none

def shimAbi : Parser (ShimAbi) := do
  let fields ← object ({} : shimAbiFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "signature" => return { fields with signature := some (← shim_signature) }
    | "query" => return { fields with query := some (← shimQuery) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let signature ← need fields.signature "signature"
  let query ← need fields.query "query"
  return {
    signature, inputTypes := query.1, outputType := query.2.1, abiId := query.2.2 }

private structure namedShimAbiFields where
  name : Option (String) := none
  recipe : Option (ShimAbi) := none
  sourceTargetOpIsUlong : Option (Option Bool) := none

def namedShimAbi : Parser (NamedShimAbi) := do
  let fields ← object ({} : namedShimAbiFields) fun fields key => do
    match key with
    | "name" => return { fields with name := some (← string) }
    | "recipe" => return { fields with recipe := some (← shimAbi) }
    | "source_target_op_is_ulong" => return { fields with sourceTargetOpIsUlong := some (← nullable boolean) }
    | _ => skipValue; pure fields
  let name ← need fields.name "name"
  let recipe ← need fields.recipe "recipe"
  let sourceTargetOpIsUlong := fields.sourceTargetOpIsUlong
  return {
    name, recipe, sourceTargetOpIsUlong := sourceTargetOpIsUlong.join }

def namedTypes : Parser (Array (String × Nat)) :=
  object #[] fun entries key => do return entries.push (key, ← natural)

private structure typeLayoutsFields where
  _environment : Option (String) := none
  cratePath : Option (Array (String)) := none
  namespaceName : Option (String) := none
  entries : Option (Array (String × Nat)) := none

def typeLayouts : Parser (TypeLayouts) := do
  let fields ← object ({} : typeLayoutsFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "crate_path" => return { fields with cratePath := some (← array (string)) }
    | "namespace" => return { fields with namespaceName := some (← string) }
    | "entries" => return { fields with entries := some (← namedTypes) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let cratePath ← need fields.cratePath "crate_path"
  let namespaceName ← need fields.namespaceName "namespace"
  let entries ← need fields.entries "entries"
  return {
    cratePath, namespaceName, entries }

private structure staticQueryFields where
  definition : Option (Nat) := none
  kind : Option (String) := none
  typeId : Option (Nat) := none
  allocation : Option (Nat) := none

private def staticQuery : Parser (Nat × String × Nat × Nat) := do
  let fields ← object ({} : staticQueryFields) fun fields key => do
    match key with
    | "definition" => return { fields with definition := some (← natural) }
    | "kind" => return { fields with kind := some (← string) }
    | "type" => return { fields with typeId := some (← natural) }
    | "allocation" => return { fields with allocation := some (← natural) }
    | _ => skipValue; pure fields
  let definition ← need fields.definition "definition"
  let kind ← need fields.kind "kind"
  let typeId ← need fields.typeId "type"
  let allocation ← need fields.allocation "allocation"
  unless kind == "static" || kind == "const_allocation" do fail "unknown named global kind"
  return (definition, kind, typeId, allocation)

private structure namedStaticFields where
  _environment : Option (String) := none
  name : Option (String) := none
  path : Option (Array (String)) := none
  query : Option (Nat × String × Nat × Nat) := none

def namedStatic : Parser (NamedStatic) := do
  let fields ← object ({} : namedStaticFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "name" => return { fields with name := some (← string) }
    | "path" => return { fields with path := some (← array (string)) }
    | "query" => return { fields with query := some (← staticQuery) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let name ← need fields.name "name"
  let path ← need fields.path "path"
  let query ← need fields.query "query"
  unless path == #["libc", name] do fail "named global path does not match libc name"
  return {
    name, path, definition := query.1, isStatic := query.2.1 == "static",
    typeId := query.2.2.1, allocation := query.2.2.2 }

private structure vtableMetadataFields where
  typeId : Option (Nat) := none
  sizeBytes : Option (Option Nat) := none
  alignBytes : Option (Option Nat) := none
  principalPredicate : Option (Option Nat) := none
  predicates : Option (Array (Nat)) := none
  entries : Option (Array (VtableEntry)) := none

private def vtableMetadata : Parser (VtableAllocation) := do
  let fields ← object ({} : vtableMetadataFields) fun fields key => do
    match key with
    | "type" => return { fields with typeId := some (← natural) }
    | "size_bytes" => return { fields with sizeBytes := some (← nullable natural) }
    | "align_bytes" => return { fields with alignBytes := some (← nullable natural) }
    | "principal_predicate" => return { fields with principalPredicate := some (← nullable natural) }
    | "predicates" => return { fields with predicates := some (← array (natural)) }
    | "entries" => return { fields with entries := some (← array (DecoderValues.parseVtableEntry "$vtable.entries")) }
    | _ => skipValue; pure fields
  let typeId ← need fields.typeId "type"
  let sizeBytes ← need fields.sizeBytes "size_bytes"
  let alignBytes ← need fields.alignBytes "align_bytes"
  let principalPredicate ← need fields.principalPredicate "principal_predicate"
  let predicates ← need fields.predicates "predicates"
  let entries ← need fields.entries "entries"
  return {
    typeId, sizeBytes, alignBytes, principalPredicate, predicates, entries }

private structure vtableQueryFields where
  queryId : Option (Nat) := none
  inputType : Option (Nat) := none
  inputPredicates : Option (Array (Nat)) := none
  outputType : Option (Nat) := none
  outputPredicates : Option (Array (Nat)) := none
  outputTypeMonomorphic : Option (Bool) := none
  outputPredicatesMonomorphic : Option (Bool) := none
  vtableAllocation : Option (Option Nat) := none
  metadata : Option (VtableAllocation) := none

def vtableQuery : Parser (VtableQuery) := do
  let fields ← object ({} : vtableQueryFields) fun fields key => do
    match key with
    | "query_id" => return { fields with queryId := some (← natural) }
    | "input_type" => return { fields with inputType := some (← natural) }
    | "input_predicates" => return { fields with inputPredicates := some (← array (natural)) }
    | "output_type" => return { fields with outputType := some (← natural) }
    | "output_predicates" => return { fields with outputPredicates := some (← array (natural)) }
    | "output_type_monomorphic_enough" => return { fields with outputTypeMonomorphic := some (← boolean) }
    | "output_predicates_monomorphic_enough" => return { fields with outputPredicatesMonomorphic := some (← boolean) }
    | "vtable_allocation_id" => return { fields with vtableAllocation := some (← nullable natural) }
    | "vtable_metadata" => return { fields with metadata := some (← vtableMetadata) }
    | _ => skipValue; pure fields
  let queryId ← need fields.queryId "query_id"
  let inputType ← need fields.inputType "input_type"
  let inputPredicates ← need fields.inputPredicates "input_predicates"
  let outputType ← need fields.outputType "output_type"
  let outputPredicates ← need fields.outputPredicates "output_predicates"
  let outputTypeMonomorphic ← need fields.outputTypeMonomorphic "output_type_monomorphic_enough"
  let outputPredicatesMonomorphic ← need fields.outputPredicatesMonomorphic "output_predicates_monomorphic_enough"
  let vtableAllocation ← need fields.vtableAllocation "vtable_allocation_id"
  let metadata ← need fields.metadata "vtable_metadata"
  return {
    queryId, inputType, inputPredicates, outputType, outputPredicates, outputTypeMonomorphic, outputPredicatesMonomorphic, vtableAllocation, metadata }

private structure namedConstantQueryFields where
  instanceId : Option (Nat) := none
  typeId : Option (Nat) := none
  value : Option (MIR.ConstValue) := none

private def namedConstantQuery : Parser (Nat × Nat × MIR.ConstValue) := do
  let fields ← object ({} : namedConstantQueryFields) fun fields key => do
    match key with
    | "instance_id" => return { fields with instanceId := some (← natural) }
    | "type" => return { fields with typeId := some (← natural) }
    | "evaluation" => return { fields with value := some (← DecodeMIR.parseConstValue) }
    | _ => skipValue; pure fields
  let instanceId ← need fields.instanceId "instance_id"
  let typeId ← need fields.typeId "type"
  let value ← need fields.value "evaluation"
  return (instanceId, typeId, value)

private structure namedConstantFields where
  _environment : Option (String) := none
  name : Option (String) := none
  path : Option (Array (String)) := none
  query : Option (Nat × Nat × MIR.ConstValue) := none

def namedConstant : Parser (NamedConstant) := do
  let fields ← object ({} : namedConstantFields) fun fields key => do
    match key with
    | "typing_env" => return { fields with _environment := some (← expectedString "fully_monomorphized") }
    | "name" => return { fields with name := some (← string) }
    | "path" => return { fields with path := some (← array (string)) }
    | "query" => return { fields with query := some (← namedConstantQuery) }
    | _ => skipValue; pure fields
  let _environment ← need fields._environment "typing_env"
  let name ← need fields.name "name"
  let path ← need fields.path "path"
  let query ← need fields.query "query"
  return {
    name, path, instanceId := query.1, typeId := query.2.1, value := query.2.2 }

private structure callerLocationFields where
  value : DecodeMIR.ConstValueFields := {}
  span : Option (Nat) := none
  resultType : Option (Option Nat) := none

def callerLocation : Parser CallerLocation := do
  let fields ← object ({} : callerLocationFields) fun fields key => do
    match key with
    | "span" => return { fields with span := some (← natural) }
    | "result_type" => return { fields with resultType := some (← nullable natural) }
    | _ => return { fields with value := ← DecodeMIR.parseConstValueField fields.value key }
  let span ← need fields.span "span"
  let resultType ← need fields.resultType "result_type"
  let resultType ← need resultType "non-null result_type"
  let value ← DecodeMIR.finishConstValueFields fields.value
  return {
    span, resultType := some resultType, value }

structure QueryFields where
  session : Option (Session) := none
  runtime : Option (Runtime) := none
  frameMetadata : Option (FrameMetadata) := none
  instanceAbis : Option (Array InstanceAbi) := none
  functionFacts : Option (FunctionFacts) := none
  casts : Option (Array CastQuery) := none
  panic : Option (Array PanicQuery) := none
  nativeSignatures : Option (Array NativeSignature) := none
  retag : Option (Array RetagQuery) := none
  covariance : Option (Array CovarianceQuery) := none
  globalBytes : Option (GlobalBytes) := none
  callerLocations : Option (Array CallerLocation) := none
  main : Option (Main) := none
  primitives : Option (Primitives) := none
  vtables : Option (Array VtableQuery) := none
  namedTypes : Option (Option (Array (String × Nat))) := none
  shimAbis : Option (Option (Array ShimAbi)) := none
  namedShimAbis : Option (Option (Array NamedShimAbi)) := none
  libcTypeLayouts : Option (Option (TypeLayouts)) := none
  windowsTypeLayouts : Option (Option (TypeLayouts)) := none
  namedConstants : Option (Option (Array NamedConstant)) := none
  namedStatics : Option (Option (Array NamedStatic)) := none

def parseField (fields : QueryFields) (key : String) : Parser (Option QueryFields) := do
  match key with
  | "compiler_session_queries" => return some { fields with session := some (← session) }
  | "compiler_runtime_queries" => return some { fields with runtime := some (← runtime) }
  | "compiler_frame_metadata" => return some { fields with frameMetadata := some (← frame_metadata) }
  | "compiler_instance_abis" => return some { fields with instanceAbis := some (← array instance_abi) }
  | "compiler_function_facts" => return some { fields with functionFacts := some (← functionFacts) }
  | "compiler_cast_queries" => return some { fields with casts := some (← array castQuery) }
  | "compiler_panic_queries" => return some { fields with panic := some (← array panicQuery) }
  | "compiler_native_signature_queries" => return some { fields with nativeSignatures := some (← array native_signature) }
  | "compiler_retag_queries" => return some { fields with retag := some (← array retag_query) }
  | "compiler_covariance_queries" => return some { fields with covariance := some (← array covariance) }
  | "compiler_global_byte_queries" => return some { fields with globalBytes := some (← globalBytes) }
  | "compiler_caller_location_constants" => return some { fields with callerLocations := some (← array callerLocation) }
  | "compiler_main_queries" => return some { fields with main := some (← mainQueries) }
  | "compiler_runtime_primitives" => return some { fields with primitives := some (← primitives) }
  | "compiler_vtable_queries" => return some { fields with vtables := some (← array vtableQuery) }
  | "compiler_named_types" => return some { fields with namedTypes := some (← nullable (namedTypes)) }
  | "compiler_shim_abis" => return some { fields with shimAbis := some (← nullable (array shimAbi)) }
  | "compiler_named_shim_abis" => return some { fields with namedShimAbis := some (← nullable (array namedShimAbi)) }
  | "compiler_libc_type_layouts" => return some { fields with libcTypeLayouts := some (← nullable (typeLayouts)) }
  | "compiler_windows_type_layouts" => return some { fields with windowsTypeLayouts := some (← nullable (typeLayouts)) }
  | "compiler_named_constants" => return some { fields with namedConstants := some (← nullable (array namedConstant)) }
  | "compiler_named_statics" => return some { fields with namedStatics := some (← nullable (array namedStatic)) }
  | _ => pure none

def finish (fields : QueryFields) : Parser Queries := do
  return {
    session := ← need fields.session "compiler_session_queries"
    runtime := ← need fields.runtime "compiler_runtime_queries"
    frameMetadata := ← need fields.frameMetadata "compiler_frame_metadata"
    instanceAbis := ← need fields.instanceAbis "compiler_instance_abis"
    functionFacts := ← need fields.functionFacts "compiler_function_facts"
    casts := ← need fields.casts "compiler_cast_queries"
    panic := ← need fields.panic "compiler_panic_queries"
    nativeSignatures := ← need fields.nativeSignatures "compiler_native_signature_queries"
    retag := ← need fields.retag "compiler_retag_queries"
    covariance := ← need fields.covariance "compiler_covariance_queries"
    globalBytes := ← need fields.globalBytes "compiler_global_byte_queries"
    callerLocations := ← need fields.callerLocations "compiler_caller_location_constants"
    main := ← need fields.main "compiler_main_queries"
    primitives := ← need fields.primitives "compiler_runtime_primitives"
    vtables := ← need fields.vtables "compiler_vtable_queries"
    namedTypes := fields.namedTypes.join
    shimAbis := fields.shimAbis.join
    namedShimAbis := fields.namedShimAbis.join
    libcTypeLayouts := fields.libcTypeLayouts.join
    windowsTypeLayouts := fields.windowsTypeLayouts.join
    namedConstants := fields.namedConstants.join
    namedStatics := fields.namedStatics.join
  }

def validateQueries (ctx : DecodeMIR.Context) (queries : Queries) : Except String Unit := do
  for row in queries.callerLocations do
    let some resultType := row.resultType | throw "missing caller-location result type"
    let _ ← DecodeMIR.resolveConstValue ctx resultType row.value
  for rows in queries.namedConstants do
    for row in rows do
      let _ ← DecodeMIR.resolveConstValue ctx row.typeId row.value

end Miri.Input.CatalogDecoder
