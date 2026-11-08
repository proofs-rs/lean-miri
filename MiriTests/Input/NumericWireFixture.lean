import Miri.Input.SemanticTables

/-! Test data preparation only. Tests describe synthetic metadata as readable
records, then explicitly encode it in the current numeric wire format before
calling production decoders. This is not a decoder compatibility path. -/
namespace MiriTests.NumericWireFixture
open Lean Miri.Input

private abbrev EncodeM := StateT (Std.HashMap SemanticTables.Kind (Array Json)) (Except String)

private def intern (kind : SemanticTables.Kind) (node : Json) : EncodeM Json := do
  let nodes := (← get)[kind]?.getD #[]
  if kind == .predicate then
    let id ← node.getObjValAs? Nat "predicate_id"
    if let some old := nodes.find? (fun old => (old.getObjValAs? Nat "predicate_id").toOption == some id) then
      unless old == node do throw "conflicting synthetic predicate identity"
    else modify fun tables => tables.insert kind (nodes.push node)
    return toJson id
  if let some id := nodes.toList.findIdx? (· == node) then return toJson id
  modify fun tables => tables.insert kind (nodes.push node)
  return toJson nodes.size

private def shapeKind? (source : Json) : Option SemanticTables.Kind := do
  let .obj fields := source | failure
  if ["lo", "hi", "start", "end", "ctxt", "file"].all fields.contains then return .span
  if fields.contains "field_offsets_bytes" && fields.contains "size_bytes" then return .layout
  if fields.contains "arguments" && fields.contains "calling_convention" && fields.contains "fixed_count" then return .functionAbi
  if fields.toList.length == 2 && fields.contains "crate" && fields.contains "index" then return .definition
  if fields.toList.length == 3 && ["type", "layout", "mode"].all fields.contains then return .argumentAbi
  if fields.contains "regular_bits" && fields.contains "arg_extension" then return .abiAttributes
  if fields.toList.length == 2 && fields.contains "kind" && fields.contains "size_bits" then return .abiRegister
  if fields.contains "prefix_registers" && fields.contains "rest_register" then return .castTarget
  if ["type", "constant", "span", "user_type_annotation"].all fields.contains then return .constant
  if ["inputs", "output", "c_variadic"].all fields.contains then return .signature
  if fields.contains "predicate_id" && ["trait", "auto_trait", "projection"].contains
      ((source.getObjValAs? String "kind").toOption.getD "") then return .predicate
  failure

private partial def encodeValue (source : Json) (role : Option SemanticTables.Kind := none) : EncodeM Json := do
  match source with
  | .null | .num _ => return source
  | .obj fields =>
    if fields.toList.length == 1 then
      for key in ["type_id", "allocation_id", "instance_id", "predicate_id"] do
        if let .ok value := source.getObjVal? key then
          let _ ← value.getNat?
          return value
    let shapeRole := shapeKind? source
    let tag := (source.getObjValAs? String "kind").toOption.getD ""
    let mut encoded := []
    for (key, rawValue) in fields.toList do
      let value ← if tag == "ThreadLocalRef" && key == "initializer" then do
          match rawValue with
          | .obj initializer =>
            if initializer.contains "allocation" then
              if initializer.contains "allocation_template" then throw "ambiguous synthetic TLS template fields"
              pure (Json.mkObj (initializer.toList.map fun (name, child) =>
                (if name == "allocation" then "allocation_template" else name, child)))
            else pure rawValue
          | _ => pure rawValue
        else pure rawValue
      if tag == "static" && key == "allocation" && fields.contains "symbol" &&
          fields.contains "declaration" && fields.contains "allocation_query" then
        throw "ambiguous synthetic selected-static allocation fields"
      let key := if tag == "static" && key == "allocation" &&
          fields.contains "symbol" && fields.contains "declaration" then
          "allocation_query" else key
      let childRole := SemanticTables.fieldKind? key source
      let child ← if key == "line_spans" || key == "required_consts" || key == "elements" && tag == "branch" || key == "patterns" && tag == "or" then do
          match value with
          | .null => pure .null
          | _ =>
            let values ← value.getArr?
            let kind := if key == "line_spans" then SemanticTables.Kind.span
              else if key == "patterns" then .pattern else .constant
            Json.arr <$> values.mapM (fun value => encodeValue value (some kind))
        else encodeValue value childRole
      encoded := encoded ++ [(key, child)]
    let node := Json.mkObj encoded
    let role := shapeRole.orElse fun _ => role
    match role with
    | some kind => intern kind node
    | none => return node
  | .arr values =>
    let node := Json.arr (← values.mapM (fun value => encodeValue value))
    match role with | some kind => intern kind node | none => return node
  | .str text =>
    if role == some .definition then
      match text.splitOn ":" with
      | [crate, index] =>
        if let some crate := crate.toNat? then
          if let some index := index.toNat? then
            return ← intern .definition (Json.mkObj [("crate", toJson crate), ("index", toJson index)])
      | _ => pure ()
    match role with | some kind => intern kind source | none => return source
  | .bool _ =>
    match role with | some kind => intern kind source | none => return source

/-- Encode newly introduced synthetic records while retaining an input's
existing numeric tables and reference IDs. -/
def encode (document : Json) : Except String Json := do
  if (document.getObjVal? "shared_payloads").isOk then throw "obsolete synthetic shared graph; build numeric fixture explicitly"
  let mut tables := {}
  for kind in SemanticTables.kinds do
    let values := (((document.getObjVal? "semantic_tables").bind fun value =>
      value.getObjVal? kind.table).bind Json.getArr?).toOption.getD #[]
    tables := tables.insert kind values
  let fields ← document.getObj?
  let action : EncodeM Json := do
    let mut result := []
    for (key, value) in fields.toList do
      if key == "semantic_tables" then continue
      result := result ++ [(key, ← encodeValue value)]
    if !(document.getObjVal? "schema_version").isOk then
      result := result ++ [("schema_version", toJson (4 : Nat))]
    return Json.mkObj result
  let (root, finalTables) ← action.run tables
  let catalog := Json.mkObj (("schema_version", toJson (1 : Nat)) ::
    SemanticTables.kinds.toList.map (fun kind => (kind.table, Json.arr (finalTables[kind]?.getD #[]))))
  let fields ← root.getObj?
  return Json.mkObj (("semantic_tables", catalog) :: fields.toList)

end MiriTests.NumericWireFixture
