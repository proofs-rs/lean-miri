import Miri.Input.Model.Catalogs
import Miri.Input.JsonReader
import Miri.Input.GenericArgsCodec
import Miri.Input.DecoderValues
import Miri.Input.DecodeMIR
import Miri.Input.CatalogDecoderRuntime

namespace Miri.Input.CatalogDecoder
open JsonReader Catalog
abbrev Result := Except String
abbrev Value := JsonReader.Slice
private def natural := Slice.natural
private def string := Slice.string
private def boolean := Slice.boolean
private def field (j : Value) (key : String) : Result Value := j.field key
private def arrayOf (decode : Value → Result α) (j : Value) : Result (Array α) := do
  (← j.array).mapM decode
private def nullable (decode : Value → Result α) (j : Value) : Result (Option α) := do
  if j.isNull then pure none else some <$> decode j
private def optional (decode : Value → Result α) (j : Value) (key : String) : Result (Option α) := do
  match ← j.optionalField key with
  | none => pure none
  | some value => nullable decode value
private def signature (j : Value) : Result Signature := do
  let value ← DecoderValues.parseFunctionSignature j "$signature"
  return {
    inputs := value.inputs
    output := value.output
    safety := value.safety
    abi := value.abi
    cVariadic := value.cVariadic
  }

def frame_metadata (j : Value) : Result FrameMetadata := do
  return {
    localCrate := ← natural (← field j "local_crate")
    crates := ← arrayOf (fun value => do return (← (← value.field "crate").natural, ← (← value.field "name").string)) (← field j "crates")
  }

def instance_abi (j : Value) : Result InstanceAbi := do
  return {
    instanceId := ← natural (← field j "instance_id")
    extraArgumentTypes := ← (arrayOf natural) (← field j "extra_argument_types")
    abiId := ← natural (← field j "abi_query")
  }

def pointer_abi (j : Value) : Result PointerAbi := do
  return {
    typeId := ← natural (← field j "type_id")
    extraArgumentTypes := ← (arrayOf natural) (← field j "extra_argument_types")
    abiId := ← natural (← field j "abi_query")
  }

def helper_signature (j : Value) : Result HelperSignature := do
  return {
    signature := ← signature (← field j "signature")
    splatted := ← boolean (← field j "splatted")
    abiId := ← natural (← field j "abi_query")
  }

def native_signature (j : Value) : Result NativeSignature := do
  return {
    instanceId := ← natural (← field j "instance_id")
    query := ← string (← field j "query")
    normalization := ← string (← field j "normalization")
    boundRegions := ← string (← field j "bound_regions")
    signature := ← signature (← field j "signature_query")
  }

def retag_query (j : Value) : Result RetagQuery := do
  return {
    definition := ← natural (← field j "definition")
    rustcNoWritable := ← boolean (← field j "rustc_no_writable")
  }

def covariance_query (j : Value) : Result CovarianceQuery := do
  return {
    sourceType := ← natural (← field j "source_type")
    targetType := ← natural (← field j "target_type")
    value := ← boolean (← field j "value")
  }

def start_resolution (j : Value) : Result StartResolution := do
  return {
    instanceId := ← natural (← field j "instance_id")
    functionType := ← natural (← field j "function_type")
  }

def entry_signature (j : Value) : Result EntrySignature := do
  return {
    compilerSelectedEntry := ← boolean (← field j "compiler_selected_entry")
    hasBoundVariables := ← boolean (← field j "has_bound_variables")
    outputHasBoundVariables := ← boolean (← field j "output_has_bound_variables")
    returnType := ← natural (← field j "return_type")
    functionPointerType := ← natural (← field j "function_pointer_type")
    startResolution := ← (nullable start_resolution) (← field j "start_resolution")
  }

def main_entry (j : Value) : Result MainEntry := do
  return {
    definition := ← natural (← field j "definition")
    genericParameters := ← (arrayOf string) (← field j "generic_parameters")
    signature := ← entry_signature (← field j "signature_query")
  }

def compiler_entry (j : Value) : Result CompilerEntry := do
  return {
    definition := ← natural (← field j "definition")
    kind := ← string (← field j "kind")
    sigpipe := ← natural (← field j "sigpipe")
  }

def primitives (j : Value) : Result Primitives := do
  return {
    u8 := ← natural (← field j "u8")
    u16 := ← natural (← field j "u16")
    u32 := ← natural (← field j "u32")
    u64 := ← natural (← field j "u64")
    u128 := ← natural (← field j "u128")
    i8 := ← natural (← field j "i8")
    i16 := ← natural (← field j "i16")
    i32 := ← natural (← field j "i32")
    i64 := ← natural (← field j "i64")
    i128 := ← natural (← field j "i128")
    bool := ← natural (← field j "bool")
    pointerTagInteger := ← natural (← field j "pointer_tag_integer")
    usize := ← natural (← field j "usize")
    isize := ← natural (← field j "isize")
    unit := ← natural (← field j "unit")
    unitPointerConst := ← natural (← field j "unit_pointer_const")
    unitPointerMut := ← natural (← field j "unit_pointer_mut")
    immU8Pointer := ← natural (← field j "imm_u8_pointer")
    immU8PointerPointer := ← natural (← field j "imm_u8_pointer_pointer")
    typeNameResultType := ← natural (← field j "type_name_result_type")
    callerLocationType := ← optional natural j "caller_location_type"
    orderingEnum := ← optional natural j "ordering_enum"
  }

def shim_signature (j : Value) : Result ShimSignature := do
  return {
    callingConvention := ← string (← field j "calling_convention")
    arguments := ← (arrayOf string) (← field j "arguments")
    result := ← string (← field j "return")
    cVariadic := ← boolean (← field j "c_variadic")
  }

private def environment (j : Value) : Result Unit := do
  unless (← (← j.field "typing_env").string) == "fully_monomorphized" do
    throw "expected fully monomorphized compiler query"

def functionFacts (j : Value) : Result FunctionFacts := do
  let types ← arrayOf (fun row => do
    environment row
    let kind ← row.field "function_kind"
    let instanceId ← match ← (← kind.field "kind").string with
      | "function_pointer" => pure none
      | "function_definition" => some <$> (← kind.field "instance_id").natural
      | _ => throw "unknown compiler function kind"
    return {
      typeId := ← (← row.field "type_id").natural
      instanceId
      signature := ← signature (← row.field "signature_query") : FunctionType
    }) (← j.field "types")
  let pointerAbis ← arrayOf (fun row => do environment row; pointer_abi row) (← j.field "pointer_abis")
  let helperSignatures ← arrayOf (fun row => do environment row; helper_signature row) (← j.field "helper_signatures")
  return { types, pointerAbis, helperSignatures }

def castQuery (j : Value) : Result CastQuery := do
  environment j
  match ← (← j.field "query_kind").string with
  | "resolve_fn_ptr" =>
    let resolved ← match ← (← j.field "resolution_kind").string with
      | "none" =>
        if (← j.optionalField "instance_id").isSome then throw "absent function resolution carries instance"
        pure none
      | "instance" => some <$> (← j.field "instance_id").natural
      | _ => throw "unknown function resolution kind"
    return .resolveFnPtr (← (← j.field "input_type").natural) (← (← j.field "args_no_bound_vars").boolean) resolved
  | "resolve_closure_fn_once" => return .resolveClosureFnOnce (← (← j.field "input_type").natural) (← (← j.field "args_no_bound_vars").boolean) (← (← j.field "instance_id").natural)
  | "supertrait_slot" => return .supertraitSlot (← (← j.field "input_source").natural) (← (← j.field "input_target").natural) (← nullable natural (← j.field "value"))
  | "lockstep_tails" => return .lockstepTails (← (← j.field "input_source").natural) (← (← j.field "input_target").natural) (← (← j.field "source_tail").natural) (← (← j.field "target_tail").natural)
  | "box_type" => return .boxType (← (← j.field "input_type").natural) (← (← j.field "type").natural)
  | _ => throw "unknown compiler cast query"

def panicQuery (j : Value) : Result PanicQuery := do
  return {
    langItem := ← (← j.field "lang_item").string
    definition := ← nullable natural (← j.field "definition")
    genericParameters := ← optional (arrayOf string) j "generic_parameters"
  }

def globalBytes (j : Value) : Result GlobalBytes := do
  let candidates ← arrayOf (fun row => do
    let salts ← arrayOf (fun salt => do return (← (← salt.field "salt").natural,
      ← nullable natural (← salt.field "existing_allocation"))) (← row.field "salts")
    return {
      bytesHex := ← (← row.field "bytes_hex").string
      salts : GlobalByteCandidate
    }) (← j.field "candidates")
  return {
    saltCount := ← (← j.field "salt_count").natural
    strType := ← (← j.field "str_type").natural
    coveredAllocations := ← arrayOf natural (← j.field "covered_allocation_ids")
    candidates
  }

def mainQueries (j : Value) : Result Main := do
  environment j
  let linkSections ← optional (arrayOf fun row => do
    let query ← row.field "global_query"
    return {
      sectionName := ← (← row.field "section").string
      definition := ← (← row.field "definition").natural
      span := ← (← row.field "span").natural
      typeId := ← (← query.field "type").natural
      allocation := ← (← query.field "allocation").natural : LinkSection
    }) j "link_sections"
  return {
    startLangItem := ← nullable natural (← j.field "start_lang_item")
    compilerEntry := ← nullable natural (← j.field "compiler_entry")
    compilerEntryType := ← nullable compiler_entry (← j.field "compiler_entry_type")
    entries := ← arrayOf main_entry (← j.field "entries")
    linkSections
  }

def shimAbi (j : Value) : Result ShimAbi := do
  environment j
  let query ← j.field "query"
  return {
    signature := ← shim_signature (← j.field "signature")
    inputTypes := ← arrayOf natural (← query.field "input_types")
    outputType := ← (← query.field "output_type").natural
    abiId := ← (← query.field "abi_query").natural
  }

def namedShimAbi (j : Value) : Result NamedShimAbi := do
  return {
    name := ← (← j.field "name").string
    recipe := ← shimAbi (← j.field "recipe")
    sourceTargetOpIsUlong := ← optional boolean j "source_target_op_is_ulong"
  }

def typeLayouts (j : Value) : Result TypeLayouts := do
  environment j
  let entries ← (← (← j.field "entries").object).mapM fun (name, value) => do return (name, ← value.natural)
  return {
    cratePath := ← arrayOf string (← j.field "crate_path")
    namespaceName := ← (← j.field "namespace").string
    entries
  }

def namedConstant (ctx : DecodeMIR.Context) (j : Value) : Result NamedConstant := do
  environment j
  let query ← j.field "query"
  let typeId ← (← query.field "type").natural
  return {
    name := ← (← j.field "name").string
    path := ← arrayOf string (← j.field "path")
    instanceId := ← (← query.field "instance_id").natural
    typeId
    value := ← DecodeMIR.decodeConstValue ctx typeId (← query.field "evaluation")
  }

def namedStatic (j : Value) : Result NamedStatic := do
  environment j
  let query ← j.field "query"
  let kind ← (← query.field "kind").string
  unless kind == "static" || kind == "const_allocation" do throw "unknown named global kind"
  return {
    name := ← (← j.field "name").string
    path := ← arrayOf string (← j.field "path")
    definition := ← (← query.field "definition").natural
    isStatic := kind == "static"
    typeId := ← (← query.field "type").natural
    allocation := ← (← query.field "allocation").natural
  }

def vtableQuery (j : Value) : Result VtableQuery := do
  let metadata ← j.field "vtable_metadata"
  let value : VtableAllocation := {
    typeId := ← (← metadata.field "type").natural
    sizeBytes := ← nullable natural (← metadata.field "size_bytes")
    alignBytes := ← nullable natural (← metadata.field "align_bytes")
    principalPredicate := ← nullable natural (← metadata.field "principal_predicate")
    predicates := ← arrayOf natural (← metadata.field "predicates")
    entries := ← arrayOf (fun row => DecoderValues.parseVtableEntry row "$vtable.entries") (← metadata.field "entries")
  }
  return {
    queryId := ← (← j.field "query_id").natural
    inputType := ← (← j.field "input_type").natural
    inputPredicates := ← arrayOf natural (← j.field "input_predicates")
    outputType := ← (← j.field "output_type").natural
    outputPredicates := ← arrayOf natural (← j.field "output_predicates")
    outputTypeMonomorphic := ← (← j.field "output_type_monomorphic_enough").boolean
    outputPredicatesMonomorphic := ← (← j.field "output_predicates_monomorphic_enough").boolean
    vtableAllocation := ← nullable natural (← j.field "vtable_allocation_id")
    metadata := value
  }

private def covariance (row : Value) : Result CovarianceQuery := do
  environment row
  unless (← (← row.field "variance").string) == "covariant" do
    throw "expected covariant query"
  covariance_query row

def decode (ctx : DecodeMIR.Context) (j : Value) : Result Queries := do
  let root ← j.object
  let rootField (name : String) : Result Value := do
    let some (_, value) := root.find? (fun entry => entry.1 == name) | throw s!"missing field `{name}`"
    pure value
  let rootOptional {α : Type} (decode : Value → Result α) (name : String) : Result (Option α) := do
    match root.find? (fun entry => entry.1 == name) with
    | none => pure none
    | some (_, value) => nullable decode value
  let typeNames ← arrayOf (fun row => do
    environment row
    let resultType ← (← row.field "result_type").natural
    return {
      inputType := ← (← row.field "input_type").natural
      resultType
      value := ← DecodeMIR.decodeConstValue ctx resultType row : TypeName
    }) (← rootField "compiler_type_name_constants")
  let callerLocations ← arrayOf (fun row => do
    let resultType ← nullable natural (← row.field "result_type")
    let typeId ← match resultType with
      | some id => pure id
      | none => throw "caller location constant lacks result type"
    return {
      span := ← (← row.field "span").natural
      resultType
      value := ← DecodeMIR.decodeConstValue ctx typeId row : CallerLocation
    }) (← rootField "compiler_caller_location_constants")
  let namedTypes ← rootOptional (fun row => do
    (← row.object).mapM fun (name, value) => do return (name, ← value.natural)) "compiler_named_types"
  return {
    session := ← session (← rootField "compiler_session_queries")
    runtime := ← runtime (← rootField "compiler_runtime_queries")
    frameMetadata := ← frame_metadata (← rootField "compiler_frame_metadata")
    instanceAbis := ← arrayOf (fun row => do environment row; instance_abi row) (← rootField "compiler_instance_abis")
    functionFacts := ← functionFacts (← rootField "compiler_function_facts")
    casts := ← arrayOf castQuery (← rootField "compiler_cast_queries")
    typeNames
    panic := ← arrayOf panicQuery (← rootField "compiler_panic_queries")
    nativeSignatures := ← arrayOf native_signature (← rootField "compiler_native_signature_queries")
    retag := ← arrayOf retag_query (← rootField "compiler_retag_queries")
    covariance := ← arrayOf covariance (← rootField "compiler_covariance_queries")
    globalBytes := ← globalBytes (← rootField "compiler_global_byte_queries")
    callerLocations
    main := ← mainQueries (← rootField "compiler_main_queries")
    primitives := ← primitives (← rootField "compiler_runtime_primitives")
    vtables := ← arrayOf vtableQuery (← rootField "compiler_vtable_queries")
    namedTypes
    shimAbis := ← rootOptional (arrayOf shimAbi) "compiler_shim_abis"
    namedShimAbis := ← rootOptional (arrayOf namedShimAbi) "compiler_named_shim_abis"
    libcTypeLayouts := ← rootOptional typeLayouts "compiler_libc_type_layouts"
    windowsTypeLayouts := ← rootOptional typeLayouts "compiler_windows_type_layouts"
    namedConstants := ← rootOptional (arrayOf (namedConstant ctx)) "compiler_named_constants"
    namedStatics := ← rootOptional (arrayOf namedStatic) "compiler_named_statics"
  }

end Miri.Input.CatalogDecoder
