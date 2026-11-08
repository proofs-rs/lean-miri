import Miri.Input

open Lean Miri.Input
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields


private partial def patternJson : CompilerPattern → Json
  | .range start finish => obj [("range", Json.arr #[start, finish])]
  | .or patterns => obj [("or", Json.arr (patterns.map patternJson))]
  | .notNull => obj [("not_null", Json.bool true)]

private def typeJson (node : TypeNode) : Json := obj [
  ("id", toJson node.id), ("display", toJson node.display),
  ("shape_kind", toJson (reprStr node.shapeKind)),
  ("shape_metadata", toJson (reprStr node.shapeMetadata)),
  ("pattern", node.pattern.map patternJson |>.getD Json.null),
  ("compiler_facts", node.compilerFacts.map (·.payload) |>.getD Json.null),
  ("signature", match node.signature with
    | none => Json.null
    | some signature => obj [
      ("inputs", toJson signature.inputs), ("output", toJson signature.output),
      ("safety", toJson signature.safety.payload), ("abi", signature.abi.payload),
      ("c_variadic", toJson signature.cVariadic)]),
  ("layout_kind", toJson (reprStr node.layout.kind)),
  ("layout", node.layout.payload), ("payload", node.payload)]

private def predicateJson (row : CompilerPredicateEvidence) : Json := obj [
  ("id", toJson row.id), ("typing_environment", toJson row.typingEnvironment),
  ("stable_key", toJson row.stableKey), ("auto_trait", toJson row.autoTrait),

  ("normalized_id", toJson row.normalizedId), ("original", row.original), ("payload", row.payload)]

private def instanceJson (node : InstanceNode) : Json := obj [
  ("id", toJson node.id), ("kind", toJson (reprStr node.kind)),
  ("def_path", toJson node.defPath), ("definition_id", toJson (reprStr node.definitionId)),
  ("body_instantiation", node.bodyInstantiation.map (fun item => obj [
    ("tag", toJson item.tag), ("payload", item.payload)]) |>.getD Json.null),
  ("body_template_is_polymorphic", toJson node.bodyTemplateIsPolymorphic),
  ("instance_args_are_monomorphic", toJson node.instanceArgsAreMonomorphic),
  ("body_payload", node.body.map (·.payload) |>.getD Json.null), ("payload", node.payload)]

private def abiJson (abi : FunctionAbi) : Json := obj [
  ("arguments", Json.arr (abi.arguments.map fun argument => obj [
    ("type_id", toJson argument.typeId), ("layout", argument.layout.map (·.payload) |>.getD Json.null),
    ("mode", argument.mode.payload), ("payload", argument.payload)])),
  ("return", obj [("type_id", toJson abi.returnValue.typeId),
    ("layout", abi.returnValue.layout.map (·.payload) |>.getD Json.null),
    ("mode", abi.returnValue.mode.payload), ("payload", abi.returnValue.payload)]),
  ("calling_convention", abi.callingConvention.payload), ("can_unwind", toJson abi.canUnwind),
  ("c_variadic", toJson abi.cVariadic), ("fixed_count", toJson abi.fixedCount),
  ("payload", abi.payload)]

private def bodyJson (body : Body) : Json := obj [
  ("source_path", toJson body.sourcePath), ("def_path", toJson body.defPath),
  ("definition_id", toJson (reprStr body.definitionId)),
  ("argument_count", toJson body.argumentCount), ("spread_argument", toJson body.spreadArgument),
  ("local_count", toJson body.locals.size), ("block_count", toJson body.blocks.size),
  ("source_scopes", toJson body.sourceScopes),
  ("promoted_payloads", Json.arr (body.promotedBodies.map (·.payload))), ("payload", body.payload)]

private def coreJson (core : ImportDocumentCore) : Json := obj [
  ("compiler_predicates", Json.arr (core.compilerPredicates.map predicateJson)),
  ("compiler_abi_layout_schema", toJson core.compilerAbiLayoutSchema),
  ("producer", obj [("miri", toJson core.producer.miriCommit), ("rustc", toJson core.producer.rustcCommit),
    ("version", toJson core.producer.rustcVersion), ("target", toJson core.producer.targetTriple)]),
  ("runtime_target_data_layout", core.runtimeTargetDataLayout.map (fun layout =>
    obj [("payload", layout.payload)]) |>.getD Json.null),

  ("types", Json.arr (core.types.map typeJson)),
  ("allocations", Json.arr (core.allocations.map fun allocation => obj [
    ("id", toJson allocation.id), ("source_alloc_id", toJson allocation.sourceAllocId),
    ("kind", toJson (reprStr allocation.kind)),
    ("memory", allocation.memory.map (·.bytesHex) |>.getD ""),
    ("payload", allocation.payload)])),
  ("compiler_alloc_id_world", toJson (reprStr core.compilerAllocIdWorld)),
  ("instances", Json.arr (core.instances.map instanceJson)),
  ("selected_scope", core.selectedScope.map (·.payload) |>.getD Json.null),
  ("function_abis", Json.arr (core.functionAbis.map abiJson)),
  ("bodies", Json.arr (core.bodies.map bodyJson)),
  ("shared_nodes", Json.arr core.sharedNodes),
  ("raw", core.raw)]

private def sameBlock (left right : BasicBlock) : Bool := Id.run do
  if left.id != right.id || left.cleanup != right.cleanup || left.payload != right.payload ||
      left.terminator.value != right.terminator.value || left.terminator.sourceInfo != right.terminator.sourceInfo ||
      left.statements.size != right.statements.size then return false
  for (a, b) in left.statements.zip right.statements do
    if a.value != b.value || a.sourceInfo != b.sourceInfo then return false
  return true

private def sameBodyCore (left right : BodyCore) : Bool := Id.run do
  if left.sourcePath != right.sourcePath || left.defPath != right.defPath ||
      left.definitionId != right.definitionId || left.phase != right.phase ||
      left.injectionPhase != right.injectionPhase || left.argumentCount != right.argumentCount ||
      left.spreadArgument != right.spreadArgument || left.sourceScopes != right.sourceScopes ||
      left.payload != right.payload || left.locals.size != right.locals.size ||
      left.blocks.size != right.blocks.size then return false
  for (a, b) in left.locals.zip right.locals do
    if a.id != b.id || a.typeId != b.typeId || a.sourceInfo != b.sourceInfo || a.payload != b.payload then return false
  for (a, b) in left.blocks.zip right.blocks do
    if !sameBlock a b then return false
  return true

private def samePromotedBody (left right : PromotedBody) : Bool :=
  left.index == right.index && left.payload == right.payload &&
    match left.body, right.body with
    | none, none => true
    | some a, some b => sameBodyCore a b
    | _, _ => false

private def sameBody (left right : Body) : Bool :=
  sameBodyCore left.toBodyCore right.toBodyCore &&
    left.promotedBodies.size == right.promotedBodies.size &&
    (left.promotedBodies.zip right.promotedBodies).all fun (a, b) => samePromotedBody a b

private def sameSelectedScope : Option SelectedScope → Option SelectedScope → Bool
  | none, none => true
  | some left, some right =>
    left.kind == right.kind && left.semantics == right.semantics &&
    decide (left.roots = right.roots) && left.payload == right.payload
  | _, _ => false

private def sameInstance (left right : InstanceNode) : Bool := Id.run do
  if left.id != right.id || left.kind != right.kind ||
      left.defPath != right.defPath || left.definitionId != right.definitionId ||
      left.bodyInstantiation != right.bodyInstantiation ||
      left.bodyTemplateIsPolymorphic != right.bodyTemplateIsPolymorphic ||
      left.instanceArgsAreMonomorphic != right.instanceArgsAreMonomorphic ||
      left.payload != right.payload || left.promotedBodies.size != right.promotedBodies.size then return false
  match left.body, right.body with
  | none, none => pure ()
  | some a, some b => if !sameBody a b then return false
  | _, _ => return false
  for (a, b) in left.promotedBodies.zip right.promotedBodies do
    if !samePromotedBody a b then return false
  return true

private def sameCore (left right : ImportDocumentCore) : Bool := Id.run do
  if coreJson left != coreJson right || !(decide (left.compilerAllocIdWorld = right.compilerAllocIdWorld)) ||
      !sameSelectedScope left.selectedScope right.selectedScope || left.allocations.map (·.data) != right.allocations.map (·.data) ||
      left.instances.map (·.bodyInstantiation) != right.instances.map (·.bodyInstantiation) ||
      left.bodies.size != right.bodies.size || left.instances.size != right.instances.size then return false
  for (a, b) in left.instances.zip right.instances do
    if !sameInstance a b then return false
  for (a, b) in left.bodies.zip right.bodies do
    if !sameBody a b then return false
  return true

private def checkOne (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  match decodeJson text, decodeRuntimeJson text with
  | .error fullError, .error runtimeError =>
    check (fullError == runtimeError) s!"{path}: hard errors differ; full={fullError}; runtime={runtimeError}"
    IO.println s!"PASS {path}: same hard error: {fullError}"
  | .ok full, .ok runtime => do
    check (sameCore full.document.toCore runtime.document)
      s!"{path}: complete ImportDocument Core projection differs"
    check (sameCore full.executionInput.document.toCore runtime.executionInput.document)
      s!"{path}: execution-input projection differs"
    IO.println s!"PASS {path}: accepted core and execution-input projections agree"
  | .error fullError, .ok _ =>
    throw (IO.userError s!"{path}: full decoder rejected but runtime decoder accepted: {fullError}")
  | .ok _, .error runtimeError =>
    throw (IO.userError s!"{path}: runtime decoder rejected but full decoder accepted: {runtimeError}")

def main (args : List String) : IO Unit := do
  check (!args.isEmpty) "usage: RuntimeDecodeEquivalence165 <input.json>..."
  for path in args do checkOne path
