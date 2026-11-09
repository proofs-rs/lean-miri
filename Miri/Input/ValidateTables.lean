import Miri.Input.Model

namespace Miri.Input

private structure ReferenceBounds where
  types : Nat
  allocations : Nat
  instances : Nat
  layouts : Nat
  abis : Nat
  spans : Nat
  definitions : Nat
  constants : Nat
  bodies : Nat
  predicates : Nat

private def checkId (count id : Nat) (path kind : String) : Except String Unit := do
  unless id < count do throw s!"{path}: dangling {kind} reference {id}"

private def boundRegion (b : ReferenceBounds) (path : String) : MIR.BoundRegionKind → Except String Unit
  | .Named id => checkId b.definitions id path "definition"
  | .Anon | .NamedForPrinting _ | .ClosureEnv => pure ()

private def boundVariable (b : ReferenceBounds) (path : String) : MIR.BoundVariableKind → Except String Unit
  | .Type (.Param id) => checkId b.definitions id path "definition"
  | .Region region => boundRegion b path region
  | .Type .Anon | .Const => pure ()

private def region (b : ReferenceBounds) (path : String) : MIR.Region → Except String Unit
  | .Bound _ _ kind | .Placeholder _ _ kind => boundRegion b path kind
  | .LateParameter scope kind => do
    checkId b.definitions scope path "definition"
    match kind with
    | .Named id => checkId b.definitions id path "definition"
    | .Anon _ | .NamedAnon _ _ | .ClosureEnv => pure ()
  | .EarlyParameter _ _ | .Static | .InferenceVariable _ | .Erased | .Error => pure ()

private def genericArgs (b : ReferenceBounds) (path : String) (args : Array MIR.GenericArg) : Except String Unit := do
  for (arg, index) in args.toList.zipIdx do
    match arg with
    | .Type id => checkId b.types id s!"{path}[{index}]" "type"
    | .Const id => checkId b.constants id s!"{path}[{index}]" "type constant"
    | .Lifetime value => region b s!"{path}[{index}]" value

private def boundVariables (b : ReferenceBounds) (path : String) (variables : Array MIR.BoundVariableKind) : Except String Unit := do
  for (binder, index) in variables.toList.zipIdx do
    boundVariable b s!"{path}[{index}]" binder

private def signature (b : ReferenceBounds) (path : String) (value : FunctionSignature) : Except String Unit := do
  for (input, index) in value.inputs.toList.zipIdx do
    checkId b.types input s!"{path}.inputs[{index}]" "type"
  checkId b.types value.output s!"{path}.output" "type"

private partial def pattern (b : ReferenceBounds) (path : String) : CompilerPattern → Except String Unit
  | .range start finish => do
    checkId b.constants start s!"{path}.start" "type constant"
    checkId b.constants finish s!"{path}.end" "type constant"
  | .or values => do
    for (value, index) in values.toList.zipIdx do pattern b s!"{path}.patterns[{index}]" value
  | .notNull => pure ()

private def typeShape (b : ReferenceBounds) (path : String) : TypeShape → Except String Unit
  | .adt data => do
    checkId b.definitions data.definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" data.args
    for (variant, vi) in data.variants.toList.zipIdx do
      for (field, fi) in variant.fields.toList.zipIdx do
        checkId b.types field.typeId s!"{path}.variants[{vi}].fields[{fi}].type" "type"
  | .foreign definition => checkId b.definitions definition s!"{path}.def_id" "definition"
  | .array element length constructor => do
    checkId b.types element s!"{path}.element" "type"
    checkId b.constants length s!"{path}.length" "type constant"
    unless constructor.count < 2^64 do throw s!"{path}.constructor.count: array count exceeds u64"
  | .patternType base value => do
    checkId b.types base s!"{path}.base" "type"
    pattern b s!"{path}.pattern" value
  | .slice element => checkId b.types element s!"{path}.element" "type"
  | .rawPointer pointee _ => checkId b.types pointee s!"{path}.pointee" "type"
  | .reference pointee _ lifetime => do
    checkId b.types pointee s!"{path}.pointee" "type"
    region b s!"{path}.region" lifetime
  | .functionDefinition definition args sig variables => do
    checkId b.definitions definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" args
    signature b s!"{path}.signature" sig
    boundVariables b s!"{path}.bound_variables" variables
  | .functionPointer sig variables => do
    signature b s!"{path}.signature" sig
    boundVariables b s!"{path}.bound_variables" variables
  | .unsafeBinder inner variables => do
    checkId b.types inner s!"{path}.inner" "type"
    boundVariables b s!"{path}.bound_variables" variables
  | .dynamicTraitObject predicates principal lifetime => do
    for (id, index) in predicates.toList.zipIdx do
      checkId b.predicates id s!"{path}.predicates[{index}]" "predicate"
    if let some id := principal then checkId b.predicates id s!"{path}.principal_predicate" "predicate"
    region b s!"{path}.region" lifetime
  | .closure definition args _ | .coroutineClosure definition args
  | .coroutine definition args | .alias _ definition args => do
    checkId b.definitions definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" args
  | .tuple elements => do
    for (id, index) in elements.toList.zipIdx do
      checkId b.types id s!"{path}.elements[{index}]" "type"
  | .bool | .char | .int _ | .uint _ | .float _ | .str | .never => pure ()

private def compilerFacts (b : ReferenceBounds) (path : String) (value : TypeCompilerFacts) : Except String Unit := do
  checkId b.types value.inputTypeId s!"{path}.input_type" "type"
  checkId b.types value.queryInputTypeId s!"{path}.query_input_type" "type"
  for (name, id) in value.typeQueries do
    if let some id := id then checkId b.types id s!"{path}.type_queries.{name}" "type"
  if let some id := value.definitionId then checkId b.definitions id s!"{path}.definition" "definition"
  if let some adt := value.adt then checkId b.definitions adt.definitionId s!"{path}.adt.definition" "definition"
  if let some queries := value.projectionQueries then
    for (parent, pi) in queries.parents.toList.zipIdx do
      checkId b.layouts parent.layoutId s!"{path}.projection_queries.parents[{pi}].layout" "layout"
      for (field, fi) in parent.fields.toList.zipIdx do
        checkId b.types field.typeId s!"{path}.projection_queries.parents[{pi}].fields[{fi}].type" "type"
        checkId b.layouts field.layoutId s!"{path}.projection_queries.parents[{pi}].fields[{fi}].layout" "layout"
  if let some (_, id) := value.simdSizeAndType then checkId b.types id s!"{path}.simd_size_and_type.element" "type"
  if let some discriminants := value.discriminants then
    for (value, index) in discriminants.values.toList.zipIdx do
      checkId b.types value.typeId s!"{path}.discriminants.values[{index}].type" "type"

private def typeConstant (b : ReferenceBounds) (path : String) : MIR.TypeConst → Except String Unit
  | .Param _ _ declaredType => do
    if let some id := declaredType then checkId b.types id s!"{path}.type" "type"
  | .Alias _ _ definition args => do
    checkId b.definitions definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" args
  | .Value ty tree => do
    checkId b.types ty s!"{path}.type" "type"
    checkId tree.nodes.size tree.root s!"{path}.value.root" "valtree node"
    for (node, index) in tree.nodes.toList.zipIdx do
      match node with
      | .Branch children =>
        for (id, ci) in children.toList.zipIdx do
          checkId b.constants id s!"{path}.value.nodes[{index}].elements[{ci}]" "type constant"
      | .Leaf _ _ => pure ()
  | .Expr _ args => genericArgs b s!"{path}.arguments" args
  | .InferVar _ | .InferFresh _ | .Bound _ _ | .Placeholder _ _ | .Error => pure ()

private def instanceKind (b : ReferenceBounds) (path : String) : Interpreter.CallInstanceKind → Except String Unit
  | .Item id | .Intrinsic id | .LlvmIntrinsic id | .Virtual id _ => checkId b.definitions id path "definition"
  | .Shim shim => do
    checkId b.definitions shim.defId s!"{path}.def_id" "definition"
    match shim with
    | .ClosureOnce _ closure _ => checkId b.definitions closure s!"{path}.closure_def_id" "definition"
    | .FnPtr _ ty | .Clone _ ty | .FnPtrAsPtr _ ty | .FnPtrFromPtr _ ty
    | .AsyncDropGlueCtor _ ty | .AsyncDropGlue _ ty => checkId b.types ty s!"{path}.type" "type"
    | .FutureDropPoll _ proxy impl => do
      checkId b.types proxy s!"{path}.proxy_coroutine_type" "type"
      checkId b.types impl s!"{path}.implementation_coroutine_type" "type"
    | .DropGlue _ ty =>
      if let some id := ty then checkId b.types id s!"{path}.drop_type" "type"
    | .VTable _ | .Reify _ _ | .ConstructCoroutineInClosure _ _ | .ThreadLocal _ => pure ()

private def sourceInfo (b : ReferenceBounds) (path : String) (value : SourceInfo) : Except String Unit :=
  checkId b.spans value.spanId s!"{path}.span" "span"

private partial def typedValue (b : ReferenceBounds) (path : String) : TypedValue → Except String Unit
  | .typeRef id => checkId b.types id path "type"
  | .allocationRef id => checkId b.allocations id path "allocation"
  | .instanceRef id => checkId b.instances id path "instance"
  | .sourceSpan id => checkId b.spans id path "span"
  | .sourceInfo value => sourceInfo b path value
  | .array values => do
    for (value, index) in values.toList.zipIdx do typedValue b s!"{path}[{index}]" value
  | .object fields | .statement _ fields | .terminator _ fields | .rvalue _ fields
  | .enumTag _ _ fields | .operand _ fields | .projection _ fields => do
    for (key, value) in fields do typedValue b s!"{path}.{key}" value
  | .scalar _ | .diagnostic _ | .localRef _ | .blockRef _
  | .binOperator _ | .unOperator _ | .userTypeProjection _ => pure ()

private def promoted (b : ReferenceBounds) (path : String) (values : Array PromotedBody) : Except String Unit := do
  for (value, index) in values.toList.zipIdx do
    if let some id := value.bodyId then checkId b.bodies id s!"{path}[{index}].body" "body"

private def memory (b : ReferenceBounds) (path : String) (value : AllocationMemory) : Except String Unit := do
  for (relocation, index) in value.relocations.toList.zipIdx do
    checkId b.allocations relocation.target s!"{path}.relocations[{index}].target" "allocation"

def validatePrimaryTables (document : ImportDocument) : Except String Unit := do
  let b : ReferenceBounds := {
    types := document.types.size
    allocations := document.allocations.size
    instances := document.instances.size
    layouts := document.layouts.size
    abis := document.functionAbis.size
    spans := document.spans.size
    definitions := document.definitions.size
    constants := document.typeConstants.size
    bodies := document.bodies.size
    predicates := document.predicates.size }
  for (node, index) in document.types.toList.zipIdx do
    let path := s!"$.types[{index}]"
    checkId b.layouts node.layoutId s!"{path}.layout" "layout"
    if let some id := node.layoutQueryInputTypeId then
      checkId b.types id s!"{path}.layout_query_input_type" "type"
    typeShape b s!"{path}.shape" node.shape
    if let some facts := node.compilerFacts then compilerFacts b s!"{path}.compiler_facts" facts
  for (value, index) in document.typeConstants.toList.zipIdx do
    typeConstant b s!"$.type_constants[{index}]" value
  for (value, index) in document.predicates.toList.zipIdx do
    let path := s!"$.predicates[{index}]"
    checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" value.genericArgs
    boundVariables b s!"{path}.bound_variables" value.boundVariables
    if let some id := value.projectionTerm then checkId b.types id s!"{path}.term" "type"
  for (value, index) in document.instances.toList.zipIdx do
    let path := s!"$.instances[{index}]"
    instanceKind b s!"{path}.instance_kind" value.instanceKind
    genericArgs b s!"{path}.generic_args" value.genericArgs
    if let some id := value.definitionId then checkId b.definitions id s!"{path}.def_id" "definition"
    if let some id := value.bodyId then checkId b.bodies id s!"{path}.body" "body"
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
  for (value, index) in document.functionAbis.toList.zipIdx do
    for (argument, ai) in (value.arguments.push value.returnValue).toList.zipIdx do
      checkId b.types argument.typeId s!"$.fn_abis[{index}].arguments[{ai}].type" "type"
      checkId b.layouts argument.layoutId s!"$.fn_abis[{index}].arguments[{ai}].layout" "layout"
  for (value, index) in document.allocations.toList.zipIdx do
    let path := s!"$.allocations[{index}]"
    if let some image := value.memory then memory b path image
    if let some data := value.data then
      match data with
      | .memory image => memory b path image
      | .function value => checkId b.instances value.instanceId s!"{path}.instance_id" "instance"
      | .static value =>
        checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
        if let some image := value.initializer then memory b s!"{path}.initializer" image
      | .typeId id => checkId b.types id s!"{path}.type" "type"
      | .vtable value =>
        checkId b.types value.typeId s!"{path}.type" "type"
        if let some id := value.principalPredicate then checkId b.predicates id s!"{path}.principal_predicate" "predicate"
        for (id, pi) in value.predicates.toList.zipIdx do
          checkId b.predicates id s!"{path}.predicates[{pi}]" "predicate"
        for (entry, ei) in value.entries.toList.zipIdx do
          if let some id := entry.instanceId then checkId b.instances id s!"{path}.entries[{ei}].instance_id" "instance"
          if let some id := entry.allocationId then checkId b.allocations id s!"{path}.entries[{ei}].allocation" "allocation"
          if let some id := entry.traitDefinitionId then checkId b.definitions id s!"{path}.entries[{ei}].trait_def_id" "definition"
  for (value, index) in document.bodies.toList.zipIdx do
    let path := s!"$.bodies[{index}]"
    checkId b.spans value.spanId s!"{path}.span" "span"
    checkId b.spans value.preambleDefSpanId s!"{path}.preamble_def_span" "span"
    for (entry, ei) in value.backtraceSpans.toList.zipIdx do
      checkId b.spans entry.spanId s!"{path}.backtrace_spans[{ei}].span" "span"
      unless entry.position.bytePosition < 2^32 do
        throw s!"{path}.backtrace_spans[{ei}]: compiler BytePos exceeds u32"
      unless entry.collapsedLo == entry.position.bytePosition do
        throw s!"{path}.backtrace_spans[{ei}]: collapsed hygiene BytePos/source-map position mismatch"
    if let some id := value.definitionId then checkId b.definitions id s!"{path}.source_def_id" "definition"
    if let some required := value.requiredConsts then
      for (constant, ci) in required.toList.zipIdx do
        typedValue b s!"{path}.required_consts[{ci}]" constant
    if let some context := value.constantQueryContext then
      checkId b.instances context.instanceId s!"{path}.constant_query_context.instance_id" "instance"
      checkId b.bodies context.normalizationBodyId s!"{path}.constant_query_context.normalization.body" "body"
      for (check, ci) in context.requiredChecks.toList.zipIdx do
        checkId b.spans check.spanId s!"{path}.constant_query_context.required_constant_checks.checks[{ci}].span" "span"
        typedValue b s!"{path}.constant_query_context.required_constant_checks.checks[{ci}].result.normalized_operand" check.normalizedOperand
        typedValue b s!"{path}.constant_query_context.required_constant_checks.checks[{ci}].result.value" check.value
    typedValue b s!"{path}.phase" value.phase
    if let some phase := value.injectionPhase then typedValue b s!"{path}.injection_phase" phase
    if let some scopes := value.sourceScopes then
      for (scope, si) in scopes.toList.zipIdx do
        unless scope.id == si do throw s!"{path}.source_scopes[{si}]: source scope ID does not match position"
        checkId b.spans scope.spanId s!"{path}.source_scopes[{si}].span" "span"
        if let some parent := scope.parent then checkId scopes.size parent s!"{path}.source_scopes[{si}].parent" "source scope"
        if let some parent := scope.inlinedParent then checkId scopes.size parent s!"{path}.source_scopes[{si}].inlined_parent_scope" "source scope"
        if let some inlined := scope.inlined then
          checkId b.instances inlined.instanceId s!"{path}.source_scopes[{si}].inlined.instance_id" "instance"
          checkId b.spans inlined.callsiteSpanId s!"{path}.source_scopes[{si}].inlined.callsite_span" "span"
    for (decl, li) in value.locals.toList.zipIdx do
      checkId b.types decl.typeId s!"{path}.locals[{li}].type" "type"
      sourceInfo b s!"{path}.locals[{li}].source_info" decl.sourceInfo
      if let some scopes := value.sourceScopes then
        checkId scopes.size decl.sourceInfo.scope s!"{path}.locals[{li}].source_info.scope" "source scope"
    for (block, bi) in value.blocks.toList.zipIdx do
      if let some resolution := block.callResolution then
        checkId b.abis resolution.fnAbiId s!"{path}.basic_blocks[{bi}].terminator.kind.resolution.fn_abi" "function ABI"
        if let some id := resolution.instanceId then
          checkId b.instances id s!"{path}.basic_blocks[{bi}].terminator.kind.resolution.instance_id" "instance"
        if let some id := resolution.functionType then
          checkId b.types id s!"{path}.basic_blocks[{bi}].terminator.kind.resolution.function_type" "type"
      for (statement, si) in block.statements.toList.zipIdx do
        sourceInfo b s!"{path}.basic_blocks[{bi}].statements[{si}].source_info" statement.sourceInfo
        if let some scopes := value.sourceScopes then
          checkId scopes.size statement.sourceInfo.scope s!"{path}.basic_blocks[{bi}].statements[{si}].source_info.scope" "source scope"
        typedValue b s!"{path}.basic_blocks[{bi}].statements[{si}].kind" statement.value
      sourceInfo b s!"{path}.basic_blocks[{bi}].terminator.source_info" block.terminator.sourceInfo
      if let some scopes := value.sourceScopes then
        checkId scopes.size block.terminator.sourceInfo.scope s!"{path}.basic_blocks[{bi}].terminator.source_info.scope" "source scope"
      typedValue b s!"{path}.basic_blocks[{bi}].terminator.kind" block.terminator.value
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
  for (value, index) in document.bodyRoots.toList.zipIdx do
    let path := s!"$.body_roots[{index}]"
    checkId b.bodies value.bodyId s!"{path}.body" "body"
    checkId b.instances value.entryInstance s!"{path}.entry_instance" "instance"
    checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
  if let some selected := document.selectedScope then
    for (root, index) in selected.roots.toList.zipIdx do
      checkId b.definitions root.definitionId s!"$.selected_scope.roots[{index}].def_id" "definition"

end Miri.Input
