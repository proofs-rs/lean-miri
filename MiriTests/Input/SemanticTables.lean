import Miri.Input.DecoderValues

namespace MiriTests.Input.SemanticTables
open Lean Miri.Input

private def catalog : Json := Json.mkObj (
  [("schema_version", toJson (1 : Nat))] ++
  SemanticTables.kinds.toList.map (fun kind => (kind.table, toJson (
    if kind == .predicate then #[Json.mkObj [("predicate_id", toJson (7 : Nat)), ("kind", toJson "trait")]]
    else if kind == .span then #[Json.mkObj [("lo", toJson (12 : Nat))]]
    else if kind == .layout then #[Json.mkObj [("size_bytes", toJson (16 : Nat))]]
    else #[]))))

private def document : Json := Json.mkObj [
  ("semantic_tables", catalog), ("span", toJson (0 : Nat)), ("layout", toJson (0 : Nat))]

private def replaceTable (source : Json) (kind : SemanticTables.Kind) (nodes : Array Json) : Json :=
  match source with
  | .obj fields => .obj (fields.insert kind.table (toJson nodes))
  | other => other

private def withCatalog (source : Json) : Json := Json.mkObj [("semantic_tables", source)]

private def typedField (source : TypedValue) (key : String) : Except String TypedValue := do
  let .object fields := source | throw s!"expected typed object at {key}"
  let some (_, value) := fields.find? (·.1 == key) | throw s!"missing typed field {key}"
  return value

private def checks : Except String Unit := do
  let tables ← SemanticTables.parse document
  let span ← tables.lookup .span (toJson (0 : Nat)) "$.span"
  let layout ← tables.lookup .layout (toJson (0 : Nat)) "$.layout"
  unless (span.getObjValAs? Nat "lo").toOption == some 12 do throw "wrong span ID space"
  unless (layout.getObjValAs? Nat "size_bytes").toOption == some 16 do throw "wrong layout ID space"
  unless (tables.lookup .span (toJson (1 : Nat)) "$.span").toOption.isNone do throw "accepted dangling reference"
  unless (tables.lookup .span (Json.mkObj [("span_id", toJson (0 : Nat))]) "$.span").toOption.isNone do
    throw "accepted object-wrapped reference"
  let predicate ← tables.lookup .predicate (toJson (7 : Nat)) "$.predicate"
  unless (predicate.getObjValAs? String "kind").toOption == some "trait" do throw "renumbered predicate identity"
  unless (tables.lookup .predicate (toJson (0 : Nat)) "$.predicate").toOption.isNone do throw "accepted predicate array index as identity"
  let selfCycle := replaceTable catalog .genericArgs #[Json.mkObj [("generic_args", toJson (0 : Nat))]]
  unless (SemanticTables.parse (withCatalog selfCycle)).toOption.isNone do throw "accepted semantic self cycle"
  let crossCycle := replaceTable (replaceTable catalog .genericArgs
    #[Json.mkObj [("region", toJson (0 : Nat))]]) .region
    #[Json.mkObj [("generic_args", toJson (0 : Nat))]]
  unless (SemanticTables.parse (withCatalog crossCycle)).toOption.isNone do throw "accepted cross-kind cycle"
  let dangling := replaceTable catalog .genericArgs #[Json.mkObj [("region", toJson (9 : Nat))]]
  unless (SemanticTables.parse (withCatalog dangling)).toOption.isNone do throw "accepted dangling catalog edge"
  let query (value : Json) := value
  let root (fields : List (String × Json)) := Json.mkObj (("semantic_tables", catalog) :: fields)
  for key in ["abi_query", "fn_abi"] do
    unless (SemanticTables.parse (root [(key, query (toJson (9 : Nat)))])).toOption.isNone do
      throw s!"accepted dangling {key}.value"
    unless (SemanticTables.parse (root [(key, query (.str "bad"))])).toOption.isNone do
      throw s!"accepted nonnumeric {key}.value"
  let cff := root [("function_kind", .str "fn_pointer"), ("signature_query", query (toJson (9 : Nat)))]
  unless (SemanticTables.parse cff).toOption.isNone do throw "accepted dangling CFF signature_query.value"
  for marker in [
      "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))",
      "instantiate_bound_regions_with_erased(closure_args.sig())"] do
    let native := root [("query", .str marker), ("signature_query", query (toJson (9 : Nat)))]
    unless (SemanticTables.parse native).toOption.isNone do throw "accepted dangling native signature_query.value"
  -- The main-entry query returns a structured record rather than a FnSig.
  let main := root [("signature_query", query (Json.mkObj [("return_type", toJson (0 : Nat))]))]
  let _ ← SemanticTables.parse main
  let validPredicate := root [("principal_predicate", toJson (7 : Nat)),
    ("input_predicates", Json.arr #[toJson (7 : Nat)])]
  let _ ← SemanticTables.parse validPredicate
  unless (SemanticTables.parse (root [("principal_predicate", toJson (0 : Nat))])).toOption.isNone do
    throw "accepted dangling principal predicate identity"
  for key in ["predicates", "input_predicates", "output_predicates"] do
    unless (SemanticTables.parse (root [(key, Json.arr #[toJson (0 : Nat)])])).toOption.isNone do
      throw s!"accepted dangling {key} identity"
  let predicateRow (original normalized : Nat) := root [
    ("predicate_id", toJson (7 : Nat)), ("stable_key", toJson (0 : Nat)),
    ("original", toJson original), ("normalization", query (toJson normalized))]
  let _ ← SemanticTables.parse (predicateRow 7 7)
  unless (SemanticTables.parse (predicateRow 9 7)).toOption.isNone do
    throw "accepted dangling original predicate identity"
  unless (SemanticTables.parse (predicateRow 7 9)).toOption.isNone do
    throw "accepted dangling normalized predicate identity"
  let definitionCatalog ← SemanticTables.parse (withCatalog (replaceTable catalog .definition
    #[Json.mkObj [("crate", toJson (0 : Nat)), ("index", toJson (3 : Nat))]]))
  let point (owner : Json) := Json.mkObj [("kind", .str "point"),
    ("point_kind", .str "expr"), ("hir_id", Json.mkObj [("owner_def_id", owner), ("local_id", toJson (7 : Nat))])]
  let pointMemo := DecoderValues.semanticDecodeMemo definitionCatalog
  let _ ← DecoderValues.decodeValue (point (toJson (0 : Nat))) "$.coverage" .any (some .coverageKind) pointMemo
  let _ ← DecoderValues.decodeRuntimeValue (.uncached (point (toJson (0 : Nat)))) "$.coverage" .any (some .coverageKind) pointMemo
  unless (DecoderValues.decodeValue (point (.str "0:3")) "$.coverage" .any (some .coverageKind) pointMemo).toOption.isNone do
    throw "legacy owner string accepted as exact DefId"
  let relocation := Json.mkObj [("storage_offset_bytes", toJson (0 : Nat)), ("target", toJson (2 : Nat))]
  let decodedRelocation ← DecoderValues.decodeValue relocation "$"
  unless (← typedField decodedRelocation "target") == .allocationRef 2 do
    throw "allocation relocation target was mistaken for a MIR block index"
  let blockEdge := Json.mkObj [("target", toJson (2 : Nat))]
  let decodedEdge ← DecoderValues.decodeValue blockEdge "$"
  unless (← typedField decodedEdge "target") == .blockRef 2 do
    throw "MIR block edge lost its scoped block-reference meaning"
  let allocationCatalogView := Json.mkObj [("covered_allocation_ids", Json.arr #[toJson (2 : Nat)]),
    ("existing_allocation", toJson (2 : Nat))]
  let decodedAllocationView ← DecoderValues.decodeValue allocationCatalogView "$"
  unless (← typedField decodedAllocationView "covered_allocation_ids") == .array #[.allocationRef 2] do
    throw "covered allocation IDs lost allocation-reference meaning"
  unless (← typedField decodedAllocationView "existing_allocation") == .allocationRef 2 do
    throw "existing allocation probe lost allocation-reference meaning"
  let sameEnvelope := query (toJson (2 : Nat))
  let mixed := Json.mkObj [
    ("compiler_named_types", Json.mkObj [("named", sameEnvelope)]),
    ("ordinary", sameEnvelope),
    ("selected_static", Json.mkObj [("allocation_query", sameEnvelope)]),
    ("compiler_runtime_primitives", Json.mkObj [("custom_primitive", toJson (2 : Nat)),
      ("ordering_enum", sameEnvelope)]),
    ("runtime_type_row", Json.mkObj [("input_type_id", toJson (0 : Nat)),
      ("mut_pointer_type", sameEnvelope), ("drop_glue", sameEnvelope)]),
    ("scalar_cast", Json.mkObj [("query_kind", .str "supertrait_slot"), ("value", toJson (2 : Nat))]),
    ("instance_cast", Json.mkObj [("query_kind", .str "resolve_fn_ptr"), ("value", toJson (2 : Nat))]),
    ("type_cast", Json.mkObj [("query_kind", .str "box_type"), ("value", toJson (2 : Nat))])]
  let typed ← DecoderValues.decodeValue mixed "$"
  let named ← typedField (← typedField typed "compiler_named_types") "named"
  unless named == .typeRef 2 do throw "named type query lost its type-reference meaning"
  let ordinary ← typedField typed "ordinary"
  unless ordinary == .scalar (toJson (2 : Nat)) do throw "ordinary scalar query was guessed to be a reference"
  let allocationQuery ← typedField (← typedField typed "selected_static") "allocation_query"
  unless allocationQuery == .allocationRef 2 do throw "selected static allocation query lost its allocation-reference meaning"
  let primitive ← typedField (← typedField typed "compiler_runtime_primitives") "custom_primitive"
  unless primitive == .typeRef 2 do throw "runtime primitive dictionary lost its type-reference meaning"
  let drop ← typedField (← typedField typed "runtime_type_row") "drop_glue"
  unless drop == .instanceRef 2 do throw "drop-glue result lost its instance-reference meaning"
  let scalar ← typedField (← typedField typed "scalar_cast") "value"
  unless scalar == .scalar (toJson (2 : Nat)) do throw "supertrait slot was guessed to be an instance ID"
  let fnInstance ← typedField (← typedField typed "instance_cast") "value"
  unless fnInstance == .instanceRef 2 do throw "cast resolution lost its instance-reference meaning"
  let typeCast ← typedField (← typedField typed "type_cast") "value"
  unless typeCast == .typeRef 2 do throw "box query lost its type-reference meaning"
  let keyType := DecoderValues.runtimeValueKey (.uncached sameEnvelope) "$" .any none none .typeQuery
  let keyInstance := DecoderValues.runtimeValueKey (.uncached sameEnvelope) "$" .any none none .instanceQuery
  unless keyType != keyInstance do throw "runtime memo conflated equal core query envelopes in different ID spaces"
  let opaqueDiagnostic := root [("diagnostic", Json.mkObj [
    ("status", .str "debug_payload"), ("region", toJson (999999 : Nat)),
    ("generic_args", .str "not a reference"),
    ("principal_predicate", toJson (-1 : Int)),
    ("obsolete_debug_shape", Json.mkObj [("type_id", .str "opaque")])])]
  let _ ← SemanticTables.parse opaqueDiagnostic
  let patternSource := replaceTable (replaceTable catalog .constant
      #[Json.mkObj [("status", .str "unsupported"), ("kind", .str "test_start")],
        Json.mkObj [("status", .str "unsupported"), ("kind", .str "test_end")]]) .pattern
    #[Json.mkObj [("kind", .str "not_null")],
      Json.mkObj [("kind", .str "range"),
        ("start", toJson (0 : Nat)), ("end", toJson (1 : Nat))],
      Json.mkObj [("kind", .str "or"),
        ("patterns", Json.arr #[toJson (0 : Nat), toJson (1 : Nat)])]]
  let patternCatalog ← SemanticTables.parse (withCatalog patternSource)
  match ← decodeCompilerPattern (toJson (2 : Nat)) patternCatalog with
  | .or children =>
    unless children.size == 2 do throw "pattern child ID sequence changed"
    match children[0]?, children[1]? with
    | some CompilerPattern.notNull, some (CompilerPattern.range start finish) =>
      unless start == toJson (0 : Nat) && finish == toJson (1 : Nat) do throw "range constant ID spaces changed"
    | _, _ => throw "numeric pattern children decoded to wrong variants"
  | _ => throw "numeric Or pattern did not decode"
  unless (decodeCompilerPattern (toJson (3 : Nat)) patternCatalog).toOption.isNone do
    throw "accepted dangling pattern reference"
  let patternCycle := replaceTable catalog .pattern
    #[Json.mkObj [("kind", .str "or"),
      ("patterns", Json.arr #[toJson (0 : Nat)])]]
  unless (SemanticTables.parse (withCatalog patternCycle)).toOption.isNone do throw "accepted recursive pattern reference cycle"
  let retained ← SharedPayloads.resolveGraph document
  unless retained.root == document do throw "rewrote numeric input JSON"
  unless retained.nodeResolutionCount == 0 do throw "expanded semantic reference graph"

#eval (show IO Unit from do
  match checks with
  | .ok () => pure ()
  | .error error => throw (IO.userError error))

end MiriTests.Input.SemanticTables
