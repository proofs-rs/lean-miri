import Miri.Input.Decoder
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-! Explicit test-only projection of retained schema-11/12 fixture payloads to
schema 13. This does not rerun rustc and is not producer correspondence evidence.
The source fixtures are immutable. Historical caller-location oracle rows supply
only the definition attributes selected by the pinned InstanceKind rule; no
missing attribute is guessed. Unwind, drop-definition and generic-prefix inputs use explicitly
hypothetical seed representatives preserving historical answers. They are not
recovered rustc material and provide no new producer, ABI, drop or generic-rebase
correspondence evidence. Tests of actual raw materials require fresh exports.
Production imports do not use this adapter. -/
namespace Miri.Input
open Lean

private def fixtureDefinition (kind : Json) : Option Nat := do
  let tag ← (kind.getObjVal? "kind" >>= Json.getStr?).toOption
  if tag == "item" || tag == "virtual" then
    (kind.getObjVal? "def_id" >>= Json.getNat?).toOption
  else if tag == "shim" then
    let shim ← (kind.getObjVal? "shim_kind" >>= Json.getStr?).toOption
    if shim == "vtable" then (kind.getObjVal? "def_id" >>= Json.getNat?).toOption else none
  else none

/-- Conservative test-only reachability check. It follows raw type/constant
references, refuses bound references and unsupported dynamic predicate graphs,
and never identifies the lost original FnDef binder (including unused vars). -/
private def fixtureBoundFreeArguments (types constants : Array Json) (args : Json) : Bool := Id.run do
  let mut pending := #[args]
  let mut seenTypes : Array Nat := #[]
  let mut seenConstants : Array Nat := #[]
  for _ in [:1000000] do
    let some value := pending.back? | return true
    pending := pending.pop
    match value with
    | .arr children => pending := pending ++ children
    | .obj fields =>
      let kind := (value.getObjVal? "kind" >>= Json.getStr?).toOption.getD ""
      if kind == "bound" || kind == "dynamic_trait_object" then return false
      let mut typeRefs : Array Nat := #[]
      let mut constantRefs : Array Nat := #[]
      if kind == "type" || kind == "const" then
        if let .ok id := value.getObjVal? "value" >>= Json.getNat? then
          if kind == "type" then typeRefs := typeRefs.push id
          else constantRefs := constantRefs.push id
      for (key, child) in fields.toArray do
        pending := pending.push child
        if ["pointee", "element", "base", "inner", "output", "type"].contains key then
          if let .ok id := child.getNat? then typeRefs := typeRefs.push id
        if ["length", "start", "end"].contains key then
          if let .ok id := child.getNat? then constantRefs := constantRefs.push id
        if key == "inputs" || key == "elements" then
          if let .ok children := child.getArr? then
            for child in children do
              if let .ok id := child.getNat? then
                if kind == "branch" then constantRefs := constantRefs.push id
                else typeRefs := typeRefs.push id
      for id in typeRefs do
        unless seenTypes.contains id do
          let some node := types[id]? | return false
          let .ok shape := node.getObjVal? "shape" | return false
          seenTypes := seenTypes.push id
          pending := pending.push shape
      for id in constantRefs do
        unless seenConstants.contains id do
          let some constant := constants[id]? | return false
          seenConstants := seenConstants.push id
          pending := pending.push constant
    | _ => pure ()
  return false

/-- Adapt known old fixtures only. Invalid and current versions pass unchanged
so production decoder guards remain the subject of negative tests. -/
def adaptLegacyFixture (source : String) : Except String String := do
  -- Preserve duplicate-member and malformed-unknown rejection before Json's
  -- object map could erase duplicate keys during test-only rewriting.
  match JsonReader.run JsonReader.skipValue source with
  | .error _ => return source
  | .ok _ => pure ()
  let raw ← Json.parse source
  let version := (raw.getObjVal? "schema_version" >>= Json.getNat?).toOption
  let oldBodyEncoding := version == some 13 && !(raw.getObjVal? "mir_templates").isOk &&
    ((raw.getObjVal? "bodies" >>= Json.getArr?).toOption.any fun bodies =>
      !bodies.isEmpty && bodies.all (fun body => !(body.getObjVal? "body_kind").isOk))
  unless version == some 11 || version == some 12 || oldBodyEncoding do return source
  let mut value := raw.setObjVal! "schema_version" (toJson (13 : Nat))
  if !(raw.getObjVal? "instance_abis").isOk then
    value := value.setObjVal! "instance_abis" (toJson (#[] : Array Json))
  if !(raw.getObjVal? "mir_templates").isOk then
    value := value.setObjVal! "mir_templates" (toJson (#[] : Array Json))
  if !(raw.getObjVal? "compiler_trait_program").isOk then
    value := value.setObjVal! "compiler_trait_program" (Json.mkObj [
      ("traits", toJson (#[] : Array Json)),
      ("constructor_scope", Json.mkObj [("kind", toJson "all_source_impls")])])
  if let .ok bodies := raw.getObjVal? "bodies" >>= Json.getArr? then
    value := value.setObjVal! "bodies" (toJson (bodies.map fun body =>
      if (body.getObjVal? "body_kind").isOk then body
      else body.setObjVal! "body_kind" (toJson "material")))
  if let .ok types := raw.getObjVal? "types" >>= Json.getArr? then
    let constants := (raw.getObjVal? "type_constants" >>= Json.getArr?).toOption.getD #[]
    value := value.setObjVal! "types" (toJson (types.map fun node => Id.run do
      if let .ok shape := node.getObjVal? "shape" then
        if (shape.getObjVal? "kind" >>= Json.getStr?) == .ok "alias" &&
            !(shape.getObjVal? "rigid").isOk then
          -- Hypothetical historical component input, not recovered rigidity.
          return node.setObjVal! "shape" (shape.setObjVal! "rigid" (toJson false))
        if (shape.getObjVal? "kind" >>= Json.getStr?) == .ok "function_definition" &&
            !(shape.getObjVal? "generic_args_bound_variables").isOk then
          if let .ok arguments := shape.getObjVal? "generic_args" then
            if fixtureBoundFreeArguments types constants arguments then
              -- Explicitly hypothetical historical component representative.
              -- The original binder, including unused variables, is unrecoverable.
              return node.setObjVal! "shape"
                (shape.setObjVal! "generic_args_bound_variables" (toJson (#[] : Array Json)))
      return node))
  if !(raw.getObjVal? "compiler_coroutine_coverage").isOk then
    if let .ok bodies := raw.getObjVal? "bodies" >>= Json.getArr? then
      value := value.setObjVal! "compiler_coroutine_coverage" (Json.mkObj [
        ("body_coroutines", toJson (bodies.map fun _ => false)),
        ("coroutines", toJson (#[] : Array Json)),
        ("auxiliary_bodies", toJson (#[] : Array Json))])
  if let .ok definitions := raw.getObjVal? "definitions" >>= Json.getArr? then
    if let .ok instances := raw.getObjVal? "instances" >>= Json.getArr? then
      if let .ok rows := do
          let runtime ← raw.getObjVal? "compiler_runtime_queries"
          runtime.getObjVal? "instances" >>= Json.getArr? then
        let mut flags : Array (Nat × Bool) := #[]
        for row in rows do
          if let .ok id := row.getObjVal? "instance_id" >>= Json.getNat? then
            if let some identityNode := instances[id]? then
              if let .ok kind := identityNode.getObjVal? "instance_kind" then
                if let some definition := fixtureDefinition kind then
                  if let .ok flag := row.getObjVal? "requires_caller_location" >>= Json.getBool? then
                    if let some (_, old) := flags.find? (·.1 == definition) then
                      unless old == flag do throw "historical caller-location definition flags conflict"
                    else flags := flags.push (definition, flag)
        let definitions := definitions.mapIdx fun id definition =>
          match flags.find? (·.1 == id) with
          | some (_, flag) => definition.setObjVal! "body_track_caller" (toJson flag)
          | none => definition
        value := value.setObjVal! "definitions" (toJson definitions)
  if let .ok instances := raw.getObjVal? "instances" >>= Json.getArr? then
    if let .ok runtime := value.getObjVal? "compiler_runtime_queries" then
      if let .ok rows := runtime.getObjVal? "virtual" >>= Json.getArr? then
        let rows := rows.map fun row => Id.run do
          if (row.getObjVal? "parent_generic_count").isOk then return row
          let some id := (row.getObjVal? "original_instance_id" >>= Json.getNat?).toOption
            | return row
          let some identityNode := instances[id]? | return row
          let some args := (identityNode.getObjVal? "generic_args" >>= Json.getArr?).toOption
            | return row
          let some first := args[0]? | return row
          unless (first.getObjVal? "kind" >>= Json.getStr?).toOption == some "type" do return row
          let some concrete := (row.getObjVal? "concrete_type" >>= Json.getNat?).toOption
            | return row
          let expected := args.set! 0 (Json.mkObj [("kind", toJson "type"), ("value", toJson concrete)])
          let some oracle := (row.getObjVal? "rebased_args" >>= Json.getArr?).toOption
            | return row
          unless expected == oracle do return row
          -- Every legal parent prefix yields this exact output. Count 1 is a
          -- synthetic component-test representative, not recovered rustc data.
          return row.setObjVal! "parent_generic_count" (toJson (1 : Nat))
        value := value.setObjVal! "compiler_runtime_queries"
          (runtime.setObjVal! "virtual" (toJson rows))
  if let .ok definitions := value.getObjVal? "definitions" >>= Json.getArr? then
    if let .ok types := raw.getObjVal? "types" >>= Json.getArr? then
      let booleanPool := (raw.getObjVal? "boolean_queries" >>= Json.getArr?).toOption.getD #[]
      let mut answers : Array (Nat × Array Bool) := #[]
      for sourceType in types do
        let some shape := (sourceType.getObjVal? "shape").toOption | continue
        unless (shape.getObjVal? "kind" >>= Json.getStr?).toOption == some "adt" do continue
        let some definition := (shape.getObjVal? "def_id" >>= Json.getNat?).toOption | continue
        let some facts := (sourceType.getObjVal? "compiler_facts").toOption | continue
        let some booleans := (facts.getObjVal? "boolean_queries").toOption | continue
        let booleans := match booleans.getNat?.toOption with
          | some index => booleanPool[index]?.getD .null
          | none => booleans
        let some answer := (booleans.getObjVal? "needs_drop" >>= Json.getBool?).toOption | continue
        if let some index := answers.findIdx? (·.1 == definition) then
          let prior := answers[index]!
          answers := answers.set! index (definition, prior.2.push answer)
        else answers := answers.push (definition, #[answer])
      let bodies := (raw.getObjVal? "bodies" >>= Json.getArr?).toOption.getD #[]
      let representative := bodies.findSome? fun body =>
        (body.getObjVal? "source_def_id" >>= Json.getNat?).toOption.bind fun id =>
          if id < definitions.size then some id else none
      let definitions := definitions.mapIdx fun id definition => Id.run do
        if (definition.getObjVal? "adt_drop").isOk then return definition
        let some (_, flags) := answers.find? (·.1 == id) | return definition
        if !flags.contains false && representative.isNone then return definition
        -- Explicit hypothetical representatives preserving historical answers.
        -- A representative function identity is not the recovered Drop impl.
        let material := Json.mkObj [
          ("manually_drop", toJson (!flags.contains true)),
          ("destructor", if !flags.contains false then toJson representative else .null)]
        return definition.setObjVal! "adt_drop" material
      value := value.setObjVal! "definitions" (toJson definitions)
  if let .ok abis := raw.getObjVal? "fn_abis" >>= Json.getArr? then
    let abis := abis.map fun abi => Id.run do
      let some flag := (abi.getObjVal? "can_unwind" >>= Json.getBool?).toOption
        | return abi
      let some fields := abi.getObj?.toOption | return abi
      -- Synthetic equivalent output for old component replays only. This is
      -- not recovered compiler ABI/configuration material or ABI validation.
      let seed := Json.mkObj [("abi", Json.mkObj [("kind", toJson "rust"), ("unwind", .null)]),
        ("definition", .null), ("panic_unwinds", toJson flag),
        ("panic_in_drop_unwinds", toJson true)]
      return Json.mkObj (("unwind_seed", seed) :: fields.toList.filter (·.1 != "can_unwind"))
    value := value.setObjVal! "fn_abis" (toJson abis)
  pure value.compress

def decodeFixture (source : String) : Except String ExecutionInput := do
  decodeJson (← adaptLegacyFixture source)

def decodeFixtureFile (path : System.FilePath) : IO (Except String ExecutionInput) := do
  try
    pure (decodeFixture (← IO.FS.readFile path))
  catch error => pure (.error s!"could not read {path}: {error}")

end Miri.Input
