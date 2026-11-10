import Miri.Input.Model

namespace Miri.Input
private def joinPath (path key : String) : String := path ++ "." ++ key

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

private def promoted (b : ReferenceBounds) (path : String) (values : Array PromotedBody) : Except String Unit := do
  for (value, index) in values.toList.zipIdx do
    if let some id := value.bodyId then checkId b.bodies id s!"{path}[{index}].body" "body"

private def memory (b : ReferenceBounds) (path : String) (value : AllocationMemory) : Except String Unit := do
  for (relocation, index) in value.relocations.toList.zipIdx do
    checkId b.allocations relocation.target s!"{path}.relocations[{index}].target" "allocation"

private def validatePrimitiveLayout (primitive : PrimitiveLayout) (path : String) : Except String Unit := do
  match primitive.kind with
  | .integer =>
    if primitive.integerKind.isNone || primitive.signed.isNone then
      throw (path ++ ": " ++ "integer primitive layout is missing integer kind or signedness")
  | .float =>
    if primitive.floatKind.isNone then throw (path ++ ": " ++ "float primitive layout is missing float kind")
  | .pointer =>
    if primitive.addressSpace.isNone then throw (path ++ ": " ++ "pointer primitive layout is missing address space")
  return ()

private def validateScalarLayout (scalar : ScalarLayout) (path : String) : Except String Unit := do
  validatePrimitiveLayout scalar.primitive (joinPath path "primitive")
  match scalar.kind with
  | .initialized =>
    if scalar.validRange.isNone then throw (path ++ ": " ++ "initialized scalar layout is missing its valid range")
  | .union => pure ()
  return ()

private def validateBackendRepr (repr : BackendRepr) (path : String) : Except String Unit := do
  for (key, scalar) in [("scalar", repr.scalar), ("first", repr.first), ("second", repr.second), ("element", repr.element)] do
    match scalar with
    | some value => validateScalarLayout value (joinPath path key)
    | none => pure ()
  return ()

private def validateCanonicalAbi (abi : CanonicalAbi) (path : String) : Except String Unit := do
  match abi.kind with
  | .arm =>
    match abi.armCall with
    | none => throw (joinPath path "arm_call" ++ ": " ++ "ARM calling convention is missing its call kind")
    | _ => pure ()
  | .interrupt =>
    match abi.interruptKind with
    | none => throw (joinPath path "interrupt_kind" ++ ": " ++ "interrupt calling convention is missing its interrupt kind")
    | _ => pure ()
  | .x86 =>
    match abi.x86Call with
    | none => throw (joinPath path "x86_call" ++ ": " ++ "x86 calling convention is missing its call kind")
    | _ => pure ()
  | _ => pure ()
  return ()

private def validateAbiRegister (reg : AbiRegister) (path : String) : Except String Unit := do
  match reg.kind with
  | .vector =>
    match reg.hintElement with
    | none => throw (joinPath path "kind.hint_element" ++ ": " ++ "vector ABI register is missing its element hint")
    | some _ => pure ()
  | _ => pure ()
  return ()

private def validateAbiPassMode (mode : AbiPassMode) (path : String) : Except String Unit := do
  match mode.castTarget with
  | some target =>
    for (register, index) in target.prefixRegisters.toList.zipIdx do
      validateAbiRegister register s!"{path}.target.prefix_registers[{index}]"
    validateAbiRegister target.restRegister (joinPath path "target.rest_register")
  | none => pure ()
  return ()

private def validateAllocationMemory (memory : AllocationMemory) (path : String) : Except String Unit := do
  match memory.mutability with
  | .mutable | .immutable => pure ()
  if memory.alignBytes == 0 then throw (joinPath path "align_bytes" ++ ": " ++ "allocation alignment must be nonzero")
  return ()

private def validateTagEncoding (encoding : TagEncoding) (path : String) : Except String Unit := do
  match encoding.kind with
  | .direct => pure ()
  | .niche =>
    if encoding.untaggedVariant.isNone || encoding.nicheVariants.isNone || encoding.nicheStart.isNone then
      throw (path ++ ": " ++ "niche tag encoding is missing its structured variant range or niche start")
    match encoding.nicheVariants with
    | some (first, last) => if last < first then throw (joinPath path "niche_variants" ++ ": " ++ "inclusive niche range has its end before its start")
    | none => pure ()
  return ()

private def validatePromotedBody (promoted : Array PromotedBody) (path : String) : Except String Unit := do
  for entry in promoted do
    if entry.bodyId.isNone then
      throw (s!"{path}[{entry.index}]" ++ ": " ++ "promoted MIR body is absent; cannot import it as typed MIR")
  return ()

private def validateExtraSemantic (types : Array TypeNode) (allocations : Array AllocationNode)
    (instances : Array InstanceNode) (functionAbis : Array FunctionAbi) (bodies : Array Body)
    (layouts : Array Layout) : Except String Unit := do
  for node in types do
    let shapePath := s!"types[{node.id}].shape"
    match node.shapeKind, node.shapeMetadata.signedKind, node.shapeMetadata.unsignedKind,
        node.shapeMetadata.floatKind, node.shapeMetadata.adtKind with
    | .int, none, _, _, _ => throw (joinPath shapePath "signed_kind" ++ ": " ++ "signed integer type shape is missing its exact integer type")
    | .int, some (.known kind), _, _, _ =>
      if !kind.signed then
        throw (joinPath shapePath "signed_kind" ++ ": " ++ "signed integer type shape carries an unsigned integer kind")
    | .uint, _, none, _, _ => throw (joinPath shapePath "unsigned_kind" ++ ": " ++ "unsigned integer type shape is missing its exact integer type")
    | .uint, _, some (.known kind), _, _ =>
      if kind.signed then
        throw (joinPath shapePath "unsigned_kind" ++ ": " ++ "unsigned integer type shape carries a signed integer kind")
    | .float, _, _, none, _ => throw (joinPath shapePath "float_kind" ++ ": " ++ "float type shape is missing its exact float type")
    | .adt, _, _, _, none => throw (joinPath shapePath "adt_kind" ++ ": " ++ "ADT type shape is missing its struct/union/enum kind")
    | _, _, _, _, _ => pure ()
    let some layout := layouts[node.layoutId]? | throw s!"types[{node.id}].layout: missing layout {node.layoutId}"
    match layout.kind with
    | .layout => pure ()
    match layout.backendRepresentation with
    | some repr => validateBackendRepr repr s!"types[{node.id}].layout.backend_repr"
    | none => pure ()
    match layout.variantsLayout with
    | some variants =>
      match variants.tagEncoding with
      | some encoding => validateTagEncoding encoding s!"types[{node.id}].layout.variants.tag_encoding"
      | none => if variants.kind == .multiple then throw (s!"types[{node.id}].layout.variants.tag_encoding" ++ ": " ++ "multi-variant layout is missing tag encoding")
      match variants.tag with
      | some scalar => validateScalarLayout scalar s!"types[{node.id}].layout.variants.tag"
      | none => pure ()
      for variant in variants.variants do
        validateBackendRepr variant.backendRepr s!"types[{node.id}].layout.variants[{variant.variantIndex}].backend_repr"
    | none => pure ()
  for node in allocations do
    let allocPath := s!"allocations[{node.id}]"
    match node.kind, node.data with
    | .memory, some (.memory memory) =>
      validateAllocationMemory memory allocPath
    | .function, some (.function function) =>
      let canonical := instances.filter (·.id == function.instanceId)
      unless canonical.size == 1 do throw s!"{allocPath}: missing canonical function instance"
    | .static, some (.static static) =>
      if static.definitionPath.isEmpty then throw (s!"{allocPath}.def_path" ++ ": " ++ "static allocation is missing its definition path")
      match static.initializer, static.globalInfo with
      | some initializer, _ =>
        validateAllocationMemory initializer (joinPath allocPath "initializer")
      | none, some info =>
        if !info.foreignItem then throw (joinPath allocPath "initializer" ++ ": " ++ "non-foreign static is missing its initializer image")
      | none, none =>
        throw (joinPath allocPath "initializer" ++ ": " ++ "static without an initializer lacks exact foreign-item compiler evidence")
    | .vtable, some (.vtable _) => pure ()
    | .typeId, some (.typeId _) => pure ()
    | _, none => throw (allocPath ++ ": " ++ "supported allocation is missing its typed payload")
    | _, some _ => throw (allocPath ++ ": " ++ "allocation kind and typed payload disagree")
  for node in instances do
    if let some definition := node.definitionId then
      unless definition == node.instanceKind.defId do
        throw s!"instances[{node.id}]: canonical instance kind and definition disagree"
    match node.kind with
    | .instanceMir =>
      if node.bodyId.isNone then
        throw (s!"instances[{node.id}].body" ++ ": " ++ "instance MIR is missing its decoded body")
    | .intrinsicDispatch =>
      if node.bodyId.isSome then throw s!"instances[{node.id}].body: intrinsic identity cannot carry MIR"
      match node.instanceKind with
      | .Intrinsic _ | .LlvmIntrinsic _ => pure ()
      | _ => throw s!"instances[{node.id}].instance_kind: intrinsic dispatch requires an intrinsic identity"
      if node.definitionId.isNone then throw s!"instances[{node.id}].def_id: intrinsic identity lacks its definition"
    | .foreignItemNoMir =>
      if node.bodyId.isSome then throw s!"instances[{node.id}].body: foreign declaration cannot carry MIR"
      unless node.foreignItem == some true do
        throw s!"instances[{node.id}].foreign_item: foreign dispatch requires compiler evidence"
      if node.symbolName.getD "" |>.isEmpty then
        throw s!"instances[{node.id}].symbol_name: foreign dispatch requires a nonempty compiler symbol"
      match node.instanceKind with
      | .Item _ => pure ()
      | _ => throw s!"instances[{node.id}].instance_kind: foreign dispatch requires an Item identity"
      if node.definitionId.isNone then throw s!"instances[{node.id}].def_id: foreign identity lacks its definition"
    | .virtualDispatchTarget =>
      unless node.bodyStatus == some "not_applicable" && node.bodyId.isNone do
        throw s!"instances[{node.id}].body: virtual identity must explicitly have no MIR body"
      match node.instanceKind with
      | .Virtual _ slot =>
        unless node.dispatchSlot == some slot do
          throw s!"instances[{node.id}].dispatch_slot: virtual identity slot disagrees with its instance kind"
      | _ => throw s!"instances[{node.id}].instance_kind: virtual dispatch requires Virtual identity"
      let some (ty, _) := node.virtualIdentity |
        throw s!"instances[{node.id}].virtual_identity: virtual identity lacks its compiler function type and ABI"
      let some functionType := types[ty]? |
        throw s!"instances[{node.id}].virtual_identity.function_type: missing compiler function type"
      unless functionType.shapeKind == .functionPointer || functionType.shapeKind == .functionDefinition do
        throw s!"instances[{node.id}].virtual_identity.function_type: expected compiler function type"
    | .identityOnly =>
      if node.bodyId.isSome then
        throw (s!"instances[{node.id}].body" ++ ": " ++ "symbol identity catalog row must not provide an executable MIR body")
  for (abi, abiIndex) in functionAbis.toList.zipIdx do
    validateCanonicalAbi abi.callingConvention s!"function_abis[{abiIndex}].calling_convention"
    for (arg, argIndex) in (abi.arguments.push abi.returnValue).toList.zipIdx do
      validateAbiPassMode arg.mode s!"function_abis[{abiIndex}].arguments[{argIndex}].mode"
  for (body, index) in bodies.toList.zipIdx do
    validatePromotedBody body.promotedBodies s!"bodies[{index}].promoted_bodies"
  for node in instances do
    validatePromotedBody node.promotedBodies s!"instances[{node.id}].promoted_bodies"
  return ()

private def catalogSignature (b : ReferenceBounds) (path : String) (value : Catalog.Signature) : Except String Unit := do
  for id in value.inputs do checkId b.types id path "type"
  checkId b.types value.output path "type"

private def vtable (b : ReferenceBounds) (path : String) (value : VtableAllocation) : Except String Unit := do
  checkId b.types value.typeId s!"{path}.type" "type"
  for id in value.predicates do checkId b.predicates id path "predicate"
  if let some id := value.principalPredicate then checkId b.predicates id path "predicate"
  for entry in value.entries do
    if let some id := entry.instanceId then checkId b.instances id path "instance"
    if let some id := entry.allocationId then checkId b.allocations id path "allocation"
    if let some id := entry.traitDefinitionId then checkId b.definitions id path "definition"

private def externDeclaration (b : ReferenceBounds) (path : String) (value : Catalog.ExternDeclaration) : Except String Unit := do
  checkId b.definitions value.definition path "definition"
  checkId b.types value.typeId path "type"
  checkId b.layouts value.layoutId path "layout"

private def foreignCandidate (b : ReferenceBounds) (path : String) (value : Catalog.ForeignCandidate) : Except String Unit := do
  checkId b.definitions value.definition path "definition"
  checkId b.spans value.span path "span"
  if let some id := value.instanceId then checkId b.instances id path "instance"

private def shimAbi (b : ReferenceBounds) (path : String) (value : Catalog.ShimAbi) : Except String Unit := do
  for id in value.inputTypes do checkId b.types id path "type"
  checkId b.types value.outputType path "type"
  checkId b.abis value.abiId path "function ABI"

private def catalogs (b : ReferenceBounds) (q : Catalog.Queries) : Except String Unit := do
  checkId b.spans q.session.rootSpan "$.compiler_session.root_span" "span"
  if let some startup := q.runtime.startup then
    if let some (id, _) := startup.coreEscapeDefault then
      checkId b.definitions id "$.compiler_runtime_queries.startup.core_escape_default" "definition"
  for row in q.runtime.types do
    for id in #[row.inputType, row.mutPointerType, row.mutReferenceType] do
      checkId b.types id "$.compiler_runtime_queries.types" "type"
    if let some id := row.dropGlue then checkId b.instances id "$.compiler_runtime_queries.types.drop_glue" "instance"
  for row in q.runtime.instances do
    checkId b.instances row.instanceId "$.compiler_runtime_queries.instances" "instance"
  for row in q.runtime.virtualQueries do
    let path := "$.compiler_runtime_queries.virtual_queries"
    for id in #[row.originalInstance, row.resolved] do checkId b.instances id path "instance"
    for id in #[row.methodDefinition, row.parentTrait] do checkId b.definitions id path "definition"
    checkId b.types row.concreteType path "type"
    genericArgs b path row.rebasedArgs
    checkId b.types row.vtableQuery.inputType path "type"
    for id in row.vtableQuery.inputPredicates do checkId b.predicates id path "predicate"
    unless q.vtables.any (fun table => table.queryId == row.vtableQuery.queryId &&
        table.inputType == row.vtableQuery.inputType && table.inputPredicates == row.vtableQuery.inputPredicates) do
      throw s!"{path}: virtual call references a missing exact vtable query"
  let fs := q.runtime.foreignSymbols
  if let some rows := fs.exportedCandidates then
    for row in rows do foreignCandidate b "$.compiler_runtime_queries.foreign_symbols.exported_candidates" row
  if let some rows := fs.externDeclarations then
    for row in rows do externDeclaration b "$.compiler_runtime_queries.foreign_symbols.extern_declarations" row
  if let some rows := fs.selectedForeignFallbacks then
    for row in rows do
      match row with
      | .candidate value => foreignCandidate b "$.compiler_runtime_queries.foreign_symbols.selected_fallbacks" value
      | .ambiguous _ _ => pure ()
  if let some rows := fs.selectedExports then
    for row in rows do
      let path := "$.compiler_runtime_queries.foreign_symbols.selected_exports"
      match row with
      | .ambiguous _ _ => pure ()
      | .other _ _ definition inst =>
        checkId b.definitions definition path "definition"
        if let some id := inst then checkId b.instances id path "instance"
      | .static _ definition declaration allocation =>
        checkId b.definitions definition path "definition"
        externDeclaration b path declaration
        checkId b.allocations allocation path "allocation"
  for row in q.instanceAbis do
    let path := "$.compiler_instance_abis"
    checkId b.instances row.instanceId path "instance"
    checkId b.abis row.abiId path "function ABI"
    for id in row.extraArgumentTypes do checkId b.types id path "type"
  for row in q.functionFacts.types do
    let path := "$.compiler_function_facts.types"
    checkId b.types row.typeId path "type"
    if let some id := row.instanceId then checkId b.instances id path "instance"
    catalogSignature b path row.signature
  for row in q.functionFacts.pointerAbis do
    let path := "$.compiler_function_facts.fn_ptr_abis"
    checkId b.types row.typeId path "type"
    checkId b.abis row.abiId path "function ABI"
    for id in row.extraArgumentTypes do checkId b.types id path "type"
  for row in q.functionFacts.helperSignatures do
    catalogSignature b "$.compiler_function_facts.helper_signatures" row.signature
    checkId b.abis row.abiId "$.compiler_function_facts.helper_signatures" "function ABI"
  for row in q.casts do
    let path := "$.compiler_cast_queries"
    match row with
    | .resolveFnPtr input _ inst =>
      checkId b.types input path "type"
      if let some id := inst then checkId b.instances id path "instance"
    | .resolveClosureFnOnce input _ inst =>
      checkId b.types input path "type"
      checkId b.instances inst path "instance"
    | .supertraitSlot source target _ | .boxType source target =>
      checkId b.types source path "type"
      checkId b.types target path "type"
    | .lockstepTails source target sourceTail targetTail =>
      for id in #[source, target, sourceTail, targetTail] do checkId b.types id path "type"
  for row in q.typeNames do
    for id in #[row.inputType, row.resultType] do checkId b.types id "$.compiler_type_name_constants" "type"
  for row in q.callerLocations do
    checkId b.spans row.span "$.compiler_caller_location_constants" "span"
    if let some id := row.resultType then checkId b.types id "$.compiler_caller_location_constants" "type"
  for row in q.nativeSignatures do
    checkId b.instances row.instanceId "$.compiler_native_signatures" "instance"
    catalogSignature b "$.compiler_native_signatures" row.signature
  for row in q.panic do
    if let some id := row.definition then checkId b.definitions id "$.compiler_panic_queries" "definition"
  for row in q.retag do checkId b.definitions row.definition "$.compiler_retag_queries" "definition"
  for row in q.covariance do
    checkId b.types row.sourceType "$.compiler_covariance_queries" "type"
    checkId b.types row.targetType "$.compiler_covariance_queries" "type"
  checkId b.types q.globalBytes.strType "$.compiler_global_byte_queries.str_type" "type"
  for id in q.globalBytes.coveredAllocations do checkId b.allocations id "$.compiler_global_byte_queries.covered_allocations" "allocation"
  for row in q.globalBytes.candidates do
    for (_, allocation) in row.salts do
      if let some id := allocation then checkId b.allocations id "$.compiler_global_byte_queries.candidates" "allocation"
  if let some id := q.main.startLangItem then checkId b.definitions id "$.compiler_main.start_lang_item" "definition"
  if let some id := q.main.compilerEntry then checkId b.definitions id "$.compiler_main.compiler_entry" "definition"
  if let some row := q.main.compilerEntryType then checkId b.definitions row.definition "$.compiler_main.compiler_entry_type" "definition"
  for row in q.main.entries do
    let path := "$.compiler_main.entries"
    checkId b.definitions row.definition path "definition"
    checkId b.types row.signature.returnType path "type"
    checkId b.types row.signature.functionPointerType path "type"
    if let some start := row.signature.startResolution then
      checkId b.instances start.instanceId path "instance"
      checkId b.types start.functionType path "type"
  if let some rows := q.main.linkSections then
    for row in rows do
      let path := "$.compiler_main.link_sections"
      checkId b.definitions row.definition path "definition"
      checkId b.spans row.span path "span"
      checkId b.types row.typeId path "type"
      checkId b.allocations row.allocation path "allocation"
  let p := q.primitives
  for id in #[p.u8,p.u16,p.u32,p.u64,p.u128,p.i8,p.i16,p.i32,p.i64,p.i128,p.bool,
      p.pointerTagInteger,p.usize,p.isize,p.unit,p.unitPointerConst,p.unitPointerMut,
      p.immU8Pointer,p.immU8PointerPointer,p.typeNameResultType] do
    checkId b.types id "$.compiler_primitive_types" "type"
  for id in #[p.callerLocationType,p.orderingEnum] do
    if let some id := id then checkId b.types id "$.compiler_primitive_types" "type"
  for row in q.vtables do
    let path := "$.compiler_vtable_queries"
    for id in #[row.inputType,row.outputType] do checkId b.types id path "type"
    for id in row.inputPredicates ++ row.outputPredicates do checkId b.predicates id path "predicate"
    if let some id := row.vtableAllocation then checkId b.allocations id path "allocation"
    vtable b path row.metadata
  if let some rows := q.namedTypes then
    for (_,id) in rows do checkId b.types id "$.compiler_named_types" "type"
  if let some rows := q.shimAbis then
    for row in rows do shimAbi b "$.compiler_shim_abis" row
  if let some rows := q.namedShimAbis then
    for row in rows do shimAbi b "$.compiler_named_shim_abis" row.recipe
  for rows in #[q.libcTypeLayouts,q.windowsTypeLayouts] do
    if let some rows := rows then
      for (_,id) in rows.entries do checkId b.types id "$.compiler_type_layouts" "type"
  if let some rows := q.namedConstants then
    for row in rows do
      let path := "$.compiler_named_constants"
      checkId b.instances row.instanceId path "instance"
      checkId b.types row.typeId path "type"
  if let some rows := q.namedStatics then
    for row in rows do
      let path := "$.compiler_named_statics"
      checkId b.definitions row.definition path "definition"
      checkId b.types row.typeId path "type"
      checkId b.allocations row.allocation path "allocation"

private def unsizingPointee (document : ImportDocument) (id : Nat) : Option Nat := do
  let node ← document.types[id]?
  match node.shape with
  | .reference ty _ _ | .rawPointer ty _ => some ty
  | _ => some id

private def dynamicType (document : ImportDocument) (id : Nat) : Bool :=
  match document.types[id]? with
  | some node => match node.shape with | .dynamicTraitObject .. => true | _ => false
  | none => false

private def validateUpcast (document : ImportDocument) (path : String)
    (value : DynamicUpcastEvidence) : Except String Unit := do
  unless value.operandType == value.sourceType && value.castTarget == value.targetType do
    throw s!"{path}: dynamic upcast descriptor disagrees with its cast"
  unless unsizingPointee document value.sourceType == some value.sourcePointeeType &&
      unsizingPointee document value.targetType == some value.targetPointeeType do
    throw s!"{path}: dynamic upcast descriptor disagrees with its pointee types"
  let full := document.queries.casts.filter fun row => match row with
    | .lockstepTails source target _ _ => source == value.sourceType && target == value.targetType
    | _ => false
  unless full.size == 1 && full[0]? == some (.lockstepTails value.sourceType value.targetType value.sourceType value.targetType) do
    throw s!"{path}: dynamic upcast lacks its exact full-type lockstep query"
  let pointees := document.queries.casts.filter fun row => match row with
    | .lockstepTails source target _ _ => source == value.sourcePointeeType && target == value.targetPointeeType
    | _ => false
  unless pointees.size == 1 && pointees[0]? == some (.lockstepTails value.sourcePointeeType value.targetPointeeType value.sourceTailType value.targetTailType) do
    throw s!"{path}: dynamic upcast lacks its exact pointee lockstep query"
  unless dynamicType document value.sourceTailType && dynamicType document value.targetTailType &&
      value.querySource == value.sourceTailType && value.queryTarget == value.targetTailType do
    throw s!"{path}: dynamic upcast tails disagree with the compiler supertrait query"
  let slots := document.queries.casts.filter fun row => match row with
    | .supertraitSlot source target _ => source == value.sourceTailType && target == value.targetTailType
    | _ => false
  unless slots.size == 1 do throw s!"{path}: dynamic upcast requires one exact supertrait-slot query"

private def valueAllocations : MIR.ConstValue → Array Nat
  | .Scalar (.Ptr (.Allocation id _ _ _)) | .Slice id _ | .Indirect id _ => #[id]
  | _ => #[]

private def validateRequiredExecution (document : ImportDocument) : Except String Unit := do
  if document.selectedScope.isNone && document.compilerAllocIdWorld.isNone then return
  let roots := document.bodyRoots.filter fun root => match document.selectedScope with
    | none => true
    | some scope => scope.roots.any fun selected => selected.definitionId == root.definitionId && selected.defPath == root.defPath
  let mut pending : Array (Nat × Nat) := roots.flatMap fun root => #[(0, root.bodyId), (1, root.entryInstance)]
  let mut visited : Std.HashSet (Nat × Nat) := {}
  while !pending.isEmpty do
    let current := pending
    pending := #[]
    for (kind, id) in current do
      if visited.contains (kind,id) then continue
      visited := visited.insert (kind,id)
      if kind == 0 then
        let some body := document.bodies[id]? | throw "required body is absent"
        for constant in body.requiredConsts do
          let .Val value _ := constant.value
          pending := pending ++ (valueAllocations value).map (2, ·)
        for call in body.callEvidence do
          if let some call := call then
            if let some inst := call.instanceId then pending := pending.push (1, inst)
        for block in body.nodeFacts do
          for node in block do
            pending := pending ++ node.constantAllocations.map (2, ·)
            for tls in node.threadLocals do
              unless tls.info.isStatic && tls.info.threadLocal do
                throw s!"{body.sourcePath}: ThreadLocalRef lacks static/thread-local compiler evidence"
              let some image := tls.initializer | throw s!"{body.sourcePath}: ThreadLocalRef lacks initializer image"
              unless image.sizeBytes == tls.info.sizeBytes && image.alignBytes == tls.info.alignBytes do
                throw s!"{body.sourcePath}: TLS initializer size/alignment disagrees with static compiler query"
              for relocation in image.relocations do pending := pending.push (2, relocation.target)
      else if kind == 1 then
        let some inst := document.instances[id]? | throw "required instance is absent"
        if inst.kind == .identityOnly then
          throw s!"$.instances[{id}].kind: selected execution depends on a symbol identity that has no imported MIR body"
        if let some body := inst.bodyId then pending := pending.push (0, body)
      else
        let some allocation := document.allocations[id]? | throw "required allocation is absent"
        if let some data := allocation.data then
          match data with
          | .function function => pending := pending.push (1, function.instanceId)
          | .memory image =>
            for relocation in image.relocations do pending := pending.push (2, relocation.target)
          | .static value =>
            if let some image := value.initializer then
              for relocation in image.relocations do pending := pending.push (2, relocation.target)
          | .vtable value =>
            for entry in value.entries do
              if let some inst := entry.instanceId then pending := pending.push (1, inst)
              if let some allocation := entry.allocationId then pending := pending.push (2, allocation)
          | .typeId _ => pure ()

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
    if let some id := value.bodyId then
      checkId b.bodies id s!"{path}.body" "body"
      let some body := document.bodies[id]? | throw s!"{path}.body: body is absent"
      unless body.instanceId == value.id do throw s!"{path}.body: instance identity mismatch"
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
    for entry in value.promotedBodies do
      if let some childId := entry.bodyId then
        let some child := document.bodies[childId]? | throw s!"{path}.promoted_bodies: body is absent"
        unless child.instanceId == value.id do
          throw s!"{path}.promoted_bodies: instance identity mismatch"
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
    for (entry, ei) in value.backtraceSpans.toList.zipIdx do
      unless entry.position.bytePosition < 2^32 do
        throw s!"{path}.backtrace_spans[{ei}]: compiler BytePos exceeds u32"
      unless entry.collapsedLo == entry.position.bytePosition do
        throw s!"{path}.backtrace_spans[{ei}]: collapsed hygiene BytePos/source-map position mismatch"
    checkId b.instances value.instanceId s!"{path}.instance_id" "instance"
    for scope in value.sourceScopes do
      if let some inlined := scope.inlined then
        checkId b.instances inlined.instanceId path "instance"
        checkId b.spans inlined.callsiteSpanId path "span"
    for evidence in value.callEvidence do
      if let some resolution := evidence then
        checkId b.abis resolution.fnAbiId path "function ABI"
        if let some id := resolution.instanceId then checkId b.instances id path "instance"
    for facts in value.nodeFacts do
      for node in facts do
        for tls in node.threadLocals do
          checkId b.definitions tls.definition path "definition"
          if let some image := tls.initializer then memory b path image
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
    for entry in value.promotedBodies do
      if let some childId := entry.bodyId then
        let some child := document.bodies[childId]? | throw s!"{path}.promoted_bodies: body is absent"
        unless child.instanceId == value.instanceId do
          throw s!"{path}.promoted_bodies: instance identity mismatch"
  for (value, index) in document.bodyRoots.toList.zipIdx do
    let path := s!"$.body_roots[{index}]"
    checkId b.bodies value.bodyId s!"{path}.body" "body"
    checkId b.instances value.entryInstance s!"{path}.entry_instance" "instance"
    let some body := document.bodies[value.bodyId]? | throw s!"{path}.body: body is absent"
    unless body.instanceId == value.entryInstance do throw s!"{path}.body: instance identity mismatch"
    checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
    for entry in value.promotedBodies do
      if let some childId := entry.bodyId then
        let some child := document.bodies[childId]? | throw s!"{path}.promoted_bodies: body is absent"
        unless child.instanceId == value.entryInstance do
          throw s!"{path}.promoted_bodies: instance identity mismatch"
  if let some selected := document.selectedScope then
    for (root, index) in selected.roots.toList.zipIdx do
      checkId b.definitions root.definitionId s!"$.selected_scope.roots[{index}].def_id" "definition"
  catalogs b document.queries
  validateExtraSemantic document.types document.allocations document.instances
    document.functionAbis document.bodies document.layouts
  for node in document.instances do
    if let some (ty, abi) := node.virtualIdentity then
      checkId b.types ty s!"$.instances[{node.id}].virtual_identity.function_type" "type"
      checkId b.abis abi s!"$.instances[{node.id}].virtual_identity.fn_abi" "function ABI"
      let matching := document.queries.instanceAbis.filter (·.instanceId == node.id)
      unless matching.size == 1 && matching[0]?.map (·.abiId) == some abi do
        throw s!"$.instances[{node.id}].virtual_identity.fn_abi: virtual identity must match one exact full-instance FnAbi query"
    if let some id := node.fallbackInstance then checkId b.instances id s!"$.instances[{node.id}].fallback_instance" "instance"
  for body in document.bodies do
    for block in body.nodeFacts do
      for node in block do
        for upcast in node.dynamicUpcasts do validateUpcast document body.sourcePath upcast
  validateRequiredExecution document

end Miri.Input
