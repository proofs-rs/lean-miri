import MiriTests.Input.LegacyFixture
import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (label expected : String) (json : Json) : IO Unit :=
  match decodeFixture json.compress with
  | .error error => unless (error.splitOn expected).length > 1 do
      throw (IO.userError s!"{label}: expected {expected}, got {error}")
  | .ok _ => throw (IO.userError s!"{label}: malformed JSON was accepted")

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields
private def str := Json.str
private def nat (n : Nat) : Json := toJson n
private def arr (values : Array Json) : Json := .arr values

-- Mutate emitted JSON, then run the same streaming decoder as normal imports.
-- Expected error fragments ensure every case reaches its intended invariant.
def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | [] => throw (IO.userError "expected exported compiler input")
  let text ← IO.FS.readFile path
  let imported ← must (decodeFixture text)
  let json ← must (Json.parse text)
  let document := imported.document
  let types ← must ((← must (json.getObjVal? "types")).getArr?)
  let instances ← must ((← must (json.getObjVal? "instances")).getArr?)
  let constants ← must ((← must (json.getObjVal? "type_constants")).getArr?)
  let allocations ← must ((← must (json.getObjVal? "allocations")).getArr?)
  unless types.size > 0 && instances.size > 1 && allocations.size > 0 && document.definitions.size > 0 do
    throw (IO.userError "fixture needs types, multiple instances, allocations and definitions")
  let withShape (shape : Json) := json.setObjVal! "types" (arr (types.set! 0 (types[0]!.setObjVal! "shape" shape)))
  let argument (kind : String) (id : Nat) := obj [("kind", str kind), ("value", nat id)]
  let constructor (count : Nat) := obj [("count", nat count), ("canonical_value_constructor", toJson true)]
  let arrayShape (length count : Nat) := obj [("kind", str "array"), ("element", nat 0), ("length", nat length), ("constructor_identity", constructor count)]
  let closure (arg : Json) := obj [("kind", str "closure"), ("def_id", nat 0), ("generic_args", arr #[arg]), ("upvar_count", nat 0)]
  let region := obj [("kind", str "late_parameter"), ("scope_def_id", nat document.definitions.size), ("parameter", obj [("kind", str "closure_environment")])]
  reject "tuple element" "$.types[0].shape.elements[0]: dangling type reference" (withShape (obj [("kind", str "tuple"), ("elements", arr #[nat types.size])]))
  reject "array length" "$.types[0].shape.length: dangling type constant reference" (withShape (arrayShape document.typeConstants.size 0))
  reject "array constructor width" "array count exceeds u64" (withShape (arrayShape 0 (2^64)))
  reject "pattern endpoint" "$.types[0].shape.pattern.start: dangling type constant reference" (withShape (obj [("kind", str "pattern_type"), ("base", nat 0), ("pattern", obj [("kind", str "range"), ("start", nat document.typeConstants.size), ("end", nat document.typeConstants.size)])]))
  reject "owned type argument" "$.types[0].shape.generic_args[0]: dangling type reference" (withShape (closure (argument "type" types.size)))
  reject "owned constant argument" "$.types[0].shape.generic_args[0]: dangling type constant reference" (withShape (closure (argument "const" document.typeConstants.size)))
  reject "binder definition" "$.types[0].shape.bound_variables[0]: dangling definition reference" (withShape (obj [("kind", str "unsafe_binder"), ("inner", nat 0), ("bound_variables", arr #[obj [("kind", str "type"), ("type_kind", obj [("kind", str "parameter"), ("def_id", nat document.definitions.size)])]])]))
  reject "region definition" "$.types[0].shape.region: dangling definition reference" (withShape (obj [("kind", str "reference"), ("pointee", nat 0), ("mutability", obj [("kind", str "immutable")]), ("region", region)]))
  reject "dynamic predicate" "$.types[0].shape.predicates[0]: dangling predicate reference" (withShape (obj [("kind", str "dynamic_trait_object"), ("predicates", arr #[nat document.predicates.size]), ("principal_predicate", Json.null), ("region", obj [("kind", str "erased")])]))
  let withInstances (rows : Array Json) := json.setObjVal! "instances" (arr rows)
  reject "instance lifetime definition" "$.instances[0].generic_args[0]: dangling definition reference" (withInstances (instances.set! 0 (instances[0]!.setObjVal! "generic_args" (arr #[obj [("kind", str "lifetime"), ("value", region)]]))))
  -- Append instead of replacing the pool so unrelated existing references stay valid.
  let withConstant (value : Json) := json.setObjVal! "type_constants" (arr (constants.push value))
  let invalidChild := constants.size + 1
  reject "constant child" s!"$.type_constants[{constants.size}].arguments[0]: dangling type constant reference" (withConstant (obj [("kind", str "expression"), ("expression_kind", str "function_call"), ("operator", Json.null), ("arguments", arr #[argument "const" invalidChild])]))
  reject "valtree child" s!"$.type_constants[{constants.size}].value.nodes[0].elements[0]: dangling type constant reference" (withConstant (obj [("kind", str "value"), ("type", nat 0), ("value", obj [("kind", str "branch"), ("elements", arr #[nat invalidChild])])]))
  reject "duplicate instance ID" "instance IDs: expected ID" (withInstances (instances.set! 1 (instances[1]!.setObjVal! "instance_id" (nat 0))))
  reject "permuted instance IDs" "instance IDs: expected ID" (withInstances ((instances.set! 0 instances[1]!).set! 1 instances[0]!))
  reject "displaced instance ID" "instance IDs: expected ID" (withInstances (instances.set! 0 (instances[0]!.setObjVal! "instance_id" (nat instances.size))))
  reject "duplicate semantic instance" "duplicate compiler instance identity" (withInstances (instances.set! 1 (instances[0]!.setObjVal! "instance_id" (nat 1))))
  -- Schema 8 groups function allocations by instance while preserving each
  -- distinct [graph ID, source AllocId]. Wire row count is not graph ID count.
  let graphId := document.allocations.size
  let sourceId := document.allocations.foldl (fun highest node =>
    max highest ((node.sourceAllocId.map UInt64.toNat).getD 0)) 0 + 1
  unless sourceId < 2^64 do throw (IO.userError "fixture has no fresh source AllocId")
  let some instanceId := (List.range instances.size).find? (fun id =>
    !document.allocations.any (fun node => match node.data with
      | some (.function function) => function.instanceId == id
      | _ => false)) | throw (IO.userError "fixture needs an unused function instance")
  let function := obj [("kind", str "function"), ("instance_id", nat instanceId),
    ("identities", arr #[arr #[nat graphId, nat sourceId]])]
  let withFunction (row : Json) := json.setObjVal! "allocations" (arr (allocations.push row))
  let _ ← must (decodeFixture (withFunction function).compress)
  reject "legacy function identity" "function identities belong in the identity list"
    (withFunction (obj [("allocation_id", nat graphId), ("source_alloc_id", nat sourceId),
      ("kind", str "function"), ("instance_id", nat instanceId)]))
  reject "function allocation instance" s!"$.allocations[{graphId}].instance_id: dangling instance reference" (withFunction (function.setObjVal! "instance_id" (nat instances.size)))
  IO.println "parser table references passed: 12 payload cases, dense IDs, semantic identities and function allocation bounds"
