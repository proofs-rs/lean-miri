import Lean

/-! Document-local semantic reference tables. IDs have meaning only together
with their kind and owning document. Lookups return one node; they never expand
an input JSON tree or infer identity from structural hashes. -/
namespace Miri.Input.SemanticTables
open Lean

inductive Kind where
  | span | layout | functionAbi | genericArgs | region | constant | signature | binder | predicate
  | definition | instanceKind | argumentAbi | abiAttributes | abiRegister | castTarget | pattern
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

def Kind.table : Kind → String
  | .span => "spans"
  | .layout => "layouts"
  | .functionAbi => "function_abis"
  | .genericArgs => "generic_args"
  | .region => "regions"
  | .constant => "constants"
  | .signature => "signatures"
  | .binder => "binders"
  | .predicate => "predicates"
  | .definition => "definitions"
  | .instanceKind => "instance_kinds"
  | .argumentAbi => "argument_abis"
  | .abiAttributes => "abi_attributes"
  | .abiRegister => "abi_registers"
  | .castTarget => "cast_targets"
  | .pattern => "patterns"

def kinds : Array Kind := #[.span, .layout, .functionAbi, .genericArgs, .region,
  .constant, .signature, .binder, .predicate, .definition, .instanceKind, .argumentAbi,
  .abiAttributes, .abiRegister, .castTarget, .pattern]

structure Catalog where
  private mk ::
  private tables : Std.HashMap Kind (Array Json) := {}
  deriving Inhabited

def empty : Catalog := {}

/-- Reconstruct immutable schema data in kind order, including reflected
imports. Validation belongs to the document decoder and demand-time lookups. -/
def ofNodes (nodes : Array (Array Json)) : Catalog :=
  ⟨(kinds.zip nodes).foldl (fun tables (kind, values) => tables.insert kind values) {}⟩


def Catalog.nodes (catalog : Catalog) (kind : Kind) : Array Json :=
  (catalog.tables[kind]?).getD #[]

/-- Parse the kind-separated tables without traversing or copying their nodes. -/
private def parseUnchecked (document : Json) : Except String Catalog := do
  let source ← document.getObjVal? "semantic_tables"
    |>.mapError fun error => s!"$.semantic_tables: missing table catalog ({error})"
  let version ← (source.getObjVal? "schema_version").bind Json.getNat?
  unless version == 1 do throw "$.semantic_tables.schema_version: expected 1"
  let mut tables := {}
  for kind in kinds do
    let values ← (source.getObjVal? kind.table).bind Json.getArr?
      |>.mapError fun error => s!"$.semantic_tables.{kind.table}: expected node array ({error})"
    tables := tables.insert kind values
  return ⟨tables⟩

/-- A bare numeric reference is decoded in a schema-provided kind. The same
number may be present in every kind's ID space. -/
def Catalog.lookup (catalog : Catalog) (kind : Kind) (value : Json) (path : String)
    : Except String Json := do
  let id ← value.getNat? |>.mapError fun error =>
    s!"{path}: expected numeric {kind.table} reference ({error})"
  if kind == .predicate then
    let matching := (catalog.nodes kind).filter fun node =>
      (node.getObjValAs? Nat "predicate_id").toOption == some id
    if matching.size != 1 then throw s!"{path}: missing or duplicate predicate identity {id}"
    return matching[0]!
  let some node := (catalog.nodes kind)[id]?
    | throw s!"{path}: dangling {kind.table} reference {id}"
  return node

/-- Decode entry points also accept a node obtained from a checked table
lookup. This is a one-layer view, not an alternate wire reference format. -/
def Catalog.node (catalog : Catalog) (kind : Kind) (value : Json) (path : String)
    : Except String Json :=
  match value with
  | .num _ => catalog.lookup kind value path
  | _ => pure value

/-- Field roles shared by the producer and consumer. Ambiguous fields such as
`value`, `inputs`, and `output` require their parent schema, not just their name. -/
def fieldKind? (key : String) (parent : Json := .null) : Option Kind :=
  let tag := (parent.getObjValAs? String "kind").toOption.getD ""
  match key with
  | "span" | "preamble_def_span" | "callsite_span" | "function_span" | "root_span" => some .span
  | "layout" => some .layout
  | "fn_abi" | "abi_query" => some .functionAbi
  | "generic_args" | "rebased_args" => some .genericArgs
  | "arguments" => if tag == "expression" then some .genericArgs else none
  | "region" => some .region
  | "instance_kind" | "source_instance_kind" => some .instanceKind
  | "def_id" | "instance_def_id" | "trait_def_id" | "scope_def_id"
  | "method_definition" | "parent_trait" | "definition" | "owner_def_id" | "source_def_id"
  | "call_once_def_id" | "closure_def_id" | "coroutine_closure_def_id"
  | "start_lang_item" | "compiler_entry" | "hoisted_from" => some .definition
  | "normalization" => if (parent.getObjVal? "stable_key").isOk &&
      (parent.getObjVal? "predicate_id").isOk then some .predicate else none
  | "signature" => some .signature
  | "signature_query" =>
    if (parent.getObjVal? "function_kind").isOk ||
        ["instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))",
          "instantiate_bound_regions_with_erased(closure_args.sig())"].contains
          ((parent.getObjValAs? String "query").toOption.getD "") then some .signature else none
  | "pattern" => some .pattern
  | "principal_predicate" => some .predicate
  | "bound_variables" | "signature_bound_variables" => some .binder
  | "const" | "constant" | "normalized_operand" => some .constant
  | "length" => if tag == "array" then some .constant else none
  | "count" => if tag == "Repeat" then some .constant else none
  | "start" | "end" => if tag == "range" then some .constant else none
  | "value" => if tag == "lifetime" then some .region else
      if tag == "const" || tag == "sym_fn" then some .constant else none
  | _ => none

/-- Core compiler references retain their kind in the schema field, while
runtime local/block/scope indices keep their own scoped interpretation. -/
def typeField (key : String) (parent : Json) : Bool :=
  let tag := (parent.getObjValAs? String "kind").toOption.getD ""
  ["base", "cast_type", "clone_type", "coroutine_type", "drop_type",
    "element_type", "field_type", "function_type", "function_pointer_type",
    "implementation_coroutine_type", "inner", "inner_type", "input_source", "input_target",
    "input_type", "pointee", "pointee_type", "pointer_tag_integer",
    "proxy_coroutine_type", "query_input_type", "source_pointee_type", "source_tail_type",
    "source_type", "source_tail", "target_tail", "target_pointee_type", "target_tail_type", "target_type", "type",
    "type_name_result_type", "return_type", "yield_type", "resume_type",
    "result_type", "output_type", "str_type", "resulting_type", "layout_query_input_type", "implicit_overflow_tuple_type"].contains key ||
  (key == "value" && tag == "type") ||
  (key == "output" && (parent.getObjVal? "inputs").isOk) ||
  (key == "element" && tag != "simd_vector" && tag != "scalable_simd_vector")

def typeArrayField (key : String) (parent : Json) : Bool :=
  let tag := (parent.getObjValAs? String "kind").toOption.getD ""
  ["extra_argument_types", "input_types"].contains key || key == "elements" && tag == "tuple" ||
    key == "inputs" && (parent.getObjVal? "output").isOk

inductive CoreReferenceKind where
  | typeId | allocationId | instanceId
  deriving BEq, Hashable

inductive CoreReferenceContext where
  | ordinary | typeQuery | instanceQuery | allocationQuery | typeQueries | runtimePrimitives | typeLayoutCatalog
  deriving BEq, Hashable

def coreArrayKind? (parent : Json) (key : String) : Option CoreReferenceKind :=
  if typeArrayField key parent then some .typeId
  else if key == "covered_allocation_ids" then some .allocationId
  else none

/-- Source-schema contexts for core query results. Scalar queries such as
supertrait_slot are deliberately absent. These contexts do not follow types
or instances recursively into their canonical tables. -/
def coreChildContext (parent : Json) (key : String)
    (context : CoreReferenceContext := .ordinary) : CoreReferenceContext :=
  if key == "allocation_query" then .allocationQuery
  else if key == "compiler_runtime_primitives" then .runtimePrimitives
  else if ["compiler_libc_type_layouts", "compiler_windows_type_layouts"].contains key then .typeLayoutCatalog
  else if context == .typeLayoutCatalog && key == "entries" then .typeQueries
  else if key == "compiler_named_types" || key == "type_queries" then .typeQueries
  else if context == .typeQueries then .typeQuery
  else if context == .runtimePrimitives && ["caller_location_type", "ordering_enum"].contains key then .typeQuery
  else if ["mut_pointer_type", "mut_reference_type"].contains key &&
      (parent.getObjVal? "input_type_id").isOk then .typeQuery
  else if key == "drop_glue" && (parent.getObjVal? "input_type_id").isOk then .instanceQuery
  else if key == "resolved" && (parent.getObjVal? "original_instance_id").isOk &&
      (parent.getObjVal? "method_definition").isOk then .instanceQuery
  else .ordinary

def coreFieldKind? (parent : Json) (key : String) (raw : Json)
    (context : CoreReferenceContext := .ordinary) : Option CoreReferenceKind :=
  let queryKind := (parent.getObjValAs? String "query_kind").toOption.getD ""
  let childContext := coreChildContext parent key context
  if typeField key parent || context == .typeQueries || childContext == .typeQuery ||
      (key == "value" && (context == .typeQuery || queryKind == "box_type")) ||
      context == .runtimePrimitives then some .typeId
  else if key == "allocation_query" || ["allocation", "existing_allocation"].contains key || key == "target" && (parent.getObjVal? "storage_offset_bytes").isOk ||
      key == "value" && context == .allocationQuery then some .allocationId
  else if childContext == .instanceQuery || key == "instance_id" ||
      ["entry_instance", "fallback_instance", "instance"].contains key ||
      (key == "value" && (context == .instanceQuery ||
        ["resolve_fn_ptr", "resolve_closure_fn_once"].contains queryKind)) then some .instanceId
  else none

/-- Only these source queries return a reference as their `value`. Main-entry
signature evidence returns its own structured record and is not a FnSig query. -/
def queryKind? (key : String) (parent child : Json) : Option Kind :=
  let nativeQuery := (parent.getObjValAs? String "query").toOption.getD ""
  if key == "abi_query" || key == "fn_abi" && (child.getObjVal? "status").isOk && !(child.getObjVal? "calling_convention").isOk then
    some .functionAbi
  else if key == "signature_query" && ((parent.getObjVal? "function_kind").isOk ||
    ["instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))",
      "instantiate_bound_regions_with_erased(closure_args.sig())"].contains nativeQuery) then some .signature
  else if key == "normalization" && (parent.getObjVal? "stable_key").isOk &&
    (parent.getObjVal? "predicate_id").isOk then some .predicate
  else none

def childKind? (key : String) (parent : Json) (query : Option Kind := none) : Option Kind :=
  let tag := (parent.getObjValAs? String "kind").toOption.getD ""
  if key == "value" && query.isSome then query
  else if key == "original" && (parent.getObjVal? "stable_key").isOk &&
    (parent.getObjVal? "predicate_id").isOk then some .predicate
  else if key == "return" && (parent.getObjVal? "calling_convention").isOk &&
    (parent.getObjVal? "fixed_count").isOk then some .argumentAbi
  else if key == "rest_register" && (parent.getObjVal? "prefix_registers").isOk then some .abiRegister
  else if ["attributes", "metadata_attributes"].contains key &&
    (["Direct", "Indirect", "IndirectUnsized"].contains tag || (parent.getObjVal? "prefix_registers").isOk) then some .abiAttributes
  else if ["first", "second"].contains key && tag == "Pair" then some .abiAttributes
  else if key == "target" && tag == "Cast" then some .castTarget
  else fieldKind? key parent

def arrayKind? (key : String) (parent : Json) : Option Kind :=
  let tag := (parent.getObjValAs? String "kind").toOption.getD ""
  if key == "required_consts" then some .constant
  else if key == "line_spans" then some .span
  else if key == "prefix_registers" && (parent.getObjVal? "rest_register").isOk then some .abiRegister
  else if key == "arguments" && (parent.getObjVal? "calling_convention").isOk &&
    (parent.getObjVal? "fixed_count").isOk then some .argumentAbi
  else if key == "elements" && tag == "branch" then some .constant
  else if key == "patterns" && tag == "or" then some .pattern
  else if ["predicates", "input_predicates", "output_predicates", "input_predicate_ids"].contains key then some .predicate
  else none

/-- Resolve exactly the requested semantic field, preserving the JSON of all
other fields for consumers that have not demanded them. -/
def Catalog.field (catalog : Catalog) (source : Json) (key path : String)
    : Except String Json := do
  let value ← source.getObjVal? key |>.mapError fun error =>
    s!"{path}: missing/invalid field `{key}` ({error})"
  if value == .null then return value
  match childKind? key source with
  | none => return value
  | some kind => catalog.node kind value s!"{path}.{key}"

private partial def referenceEdges (value : Json) (path : String)
    (context : Option Kind := none) (query : Option Kind := none) : Except String (Array (Kind × Nat × String)) := do
  match value with
  | .obj fields =>
    if (value.getObjValAs? String "status").toOption == some "debug_payload" then return #[]
    if fields.contains "$lean_miri_shared_ref" then
      throw s!"{path}: obsolete generic shared reference"
    if fields.toList.length == 1 && ["type_id", "allocation_id", "instance_id", "predicate_id"].any fields.contains then
      throw s!"{path}: object-wrapped semantic reference; expected bare numeric ID"
    let mut edges := #[]
    for (key, child) in fields.toList do
      if key == "semantic_tables" then continue
      let childPath := s!"{path}.{key}"
      let role := childKind? key value query
      if let some kind := role then
        if child != .null then
          match child.getNat? with
          | .ok id => edges := edges.push (kind, id, childPath)
          | .error error =>
            throw s!"{childPath}: expected numeric {kind.table} reference ({error})"
      let arrayRole := arrayKind? key value
      if let some kind := arrayRole then
        unless key == "required_consts" && child == .null do
          let children ← child.getArr? |>.mapError fun error => s!"{childPath}: expected reference array ({error})"
          for (entry, index) in children.toList.zipIdx do
            let id ← entry.getNat? |>.mapError fun error => s!"{childPath}[{index}]: expected numeric reference ({error})"
            edges := edges.push (kind, id, s!"{childPath}[{index}]")
      let childQuery := queryKind? key value child
      edges := edges ++ (← referenceEdges child childPath none childQuery)
    return edges
  | .arr values =>
    let mut edges := #[]
    for (child, index) in values.toList.zipIdx do
      edges := edges ++ (← referenceEdges child s!"{path}[{index}]" context query)
    return edges
  | _ => return #[]

private abbrev VisitM := StateT (Std.HashMap (Kind × Nat) Bool) (Except String)

private partial def validateNode (catalog : Catalog) (kind : Kind) (id : Nat)
    (path : String) : VisitM Unit := do
  let key := (kind, id)
  match (← get)[key]? with
  | some true => return
  | some false => throw s!"{path}: cyclic {kind.table} reference {id}"
  | none => pure ()
  let node ← catalog.lookup kind (toJson id) path
  modify fun marks => marks.insert key false
  for (childKind, childId, childPath) in ← referenceEdges node path (some kind) do
    validateNode catalog childKind childId childPath
  modify fun marks => marks.insert key true

/-- Check each semantic node once and reject dangling references and cycles
before any recursive typed decoder can follow them. Only schema roles create
edges; ordinary numeric MIR indices and scalar values never do. -/
def parse (document : Json) : Except String Catalog := do
  let catalog ← parseUnchecked document
  let validate : VisitM Unit := do
    for kind in kinds do
      for (node, index) in (catalog.nodes kind).toList.zipIdx do
        let id ← if kind == .predicate then
            (node.getObjVal? "predicate_id").bind Json.getNat?
          else pure index
        validateNode catalog kind id s!"$.semantic_tables.{kind.table}[{index}]"
    for (kind, id, path) in ← referenceEdges document "$" do
      validateNode catalog kind id path
  let _ ← validate.run {}
  return catalog

end Miri.Input.SemanticTables
