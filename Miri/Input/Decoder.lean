import Miri.Input.Model
import Miri.Input.ValidateTables
import Miri.Input.TypeConstCodec

namespace Miri.Input
open Lean DecoderValues

private def validateDense (ids : Array Nat) (what : String) : Except String Unit := do
  for (id, index) in ids.toList.zipIdx do
    unless id == index do throw s!"{what}: expected ID {index} at table position {index}, got {id}"

private partial def validateReferences (j : Json) (path : String)
    (typeCount allocationCount instanceCount layoutCount abiCount spanCount definitionCount constantCount bodyCount predicateCount : Nat) : Except String Unit := do
  if statusOf? j == some "debug_payload" then return
  match j with
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      validateReferences value s!"{path}[{index}]" typeCount allocationCount instanceCount layoutCount abiCount spanCount definitionCount constantCount bodyCount predicateCount
  | .obj fields =>
    if hasField j "$lean_miri_shared_ref" then throw s!"{path}: generic shared references are not part of this schema"
    for (key, value) in fields.toList do
      let childPath := joinPath path key
      if let some reference := referenceField j key value then
        let (id, count, kind) := match reference with
          | .typeRef id => (id, typeCount, "type")
          | .allocationRef id => (id, allocationCount, "allocation")
          | .instanceRef id => (id, instanceCount, "instance")
          | .sourceSpan id => (id, spanCount, "span")
          | _ => (0, 1, "value")
        unless id < count do throw s!"{childPath}: dangling {kind} reference {id}"
      let extraPool :=
        if key.endsWith "def_id" || ["definition", "hoisted_from"].contains key then some (definitionCount, "definition")
        else if key == "body" then some (bodyCount, "body")
        else if ["entry_instance", "original_instance_id"].contains key then some (instanceCount, "instance")
        else if key == "value" && (j.getObjValAs? String "kind").toOption == some "const" then some (constantCount, "type constant")
        else if key == "length" && (j.getObjValAs? String "kind").toOption == some "array" then some (constantCount, "type constant")
        else if key == "count" && (j.getObjValAs? String "kind").toOption == some "Repeat" then some (constantCount, "type constant")
        else if key == "const" || ["start", "end"].contains key && (j.getObjValAs? String "kind").toOption == some "range" then some (constantCount, "type constant")
        else none
      if let some (count, kind) := extraPool then
        unless value == .null do
          let id ← value.getNat? |>.mapError fun error => s!"{childPath}: expected {kind} ID ({error})"
          unless id < count do throw s!"{childPath}: dangling {kind} reference {id}"
      if key == "elements" && (j.getObjValAs? String "kind").toOption == some "branch" then
        for element in (← value.getArr?) do
          let id ← element.getNat?
          unless id < constantCount do throw s!"{childPath}: dangling type constant reference {id}"
      if key == "line_spans" then
        for span in (← value.getArr?) do
          let id ← span.getNat?
          unless id < spanCount do throw s!"{childPath}: dangling span reference {id}"
      if key == "type_queries" then
        for (_, result) in (← objectFields value) do
          unless result == .null do
            let id ← result.getNat?
            unless id < typeCount do throw s!"{childPath}: dangling type reference {id}"
      if ["predicates", "input_predicates"].contains key && path != "$" then
        for element in (← value.getArr?) do
          let id ← element.getNat?
          unless id < predicateCount do throw s!"{childPath}: dangling predicate reference {id}"
      if ["inputs", "extra_argument_types", "extra_arguments"].contains key ||
          key == "elements" && (j.getObjValAs? String "kind").toOption == some "tuple" then
        for element in (← value.getArr?) do
          let id ← element.getNat?
          unless id < typeCount do throw s!"{childPath}: dangling type reference {id}"
      if key == "layout" || key == "fn_abi" || key == "abi_query" then
        unless value == .null do
          let id ← value.getNat? |>.mapError fun error => s!"{childPath}: expected pool ID ({error})"
          let count := if key == "layout" then layoutCount else abiCount
          unless id < count do throw s!"{childPath}: dangling pool reference {id}"
      validateReferences value childPath typeCount allocationCount instanceCount layoutCount abiCount spanCount definitionCount constantCount bodyCount predicateCount
  | _ => pure ()

private partial def validateMirIndices (j : Json) (path : String)
    (localCount : Nat) : Except String Unit := do
  if statusOf? j == some "debug_payload" then return
  match j with
  | .arr values =>
    let mut index := 0
    for value in values do
      validateMirIndices value s!"{path}[{index}]" localCount
      index := index + 1
  | .obj fields =>
    for (key, value) in fields.toList do
      if key == "local" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: expected local index ({e})"
        if id >= localCount then throw s!"{joinPath path key}: local {id} is out of range (locals={localCount})"
      if key == "projection" then
        let projections ← value.getArr? |>.mapError fun e => s!"{joinPath path key}: expected projection array ({e})"
        for (projection, index) in projections.toList.zipIdx do
          let pPath := s!"{joinPath path key}[{index}]"
          let kind ← fieldString projection "kind" pPath
          if kind == "Index" then
            let id ← fieldNat projection "local" pPath
            if id >= localCount then throw s!"{pPath}.local: local {id} is out of range (locals={localCount})"
          if kind == "ConstantIndex" then
            let _ ← fieldNat projection "offset" pPath
            let _ ← fieldNat projection "min_length" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Subslice" then
            let _ ← fieldNat projection "from" pPath
            let _ ← fieldNat projection "to" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Field" then
            let _ ← fieldNat projection "index" pPath
            let _ ← field projection "field_type" pPath
          if kind == "Downcast" then
            let _ ← fieldNat projection "variant_index" pPath
          if kind == "OpaqueCast" then let _ ← field projection "cast_type" pPath
          if kind == "UnwrapUnsafeBinder" then let _ ← field projection "inner_type" pPath
          if isKnownProjection kind then let _ ← field projection "resulting_type" pPath
      validateMirIndices value (joinPath path key) localCount
  | _ => pure ()

private def checkBlockIndex (value : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let id ← value.getNat? |>.mapError fun e => s!"{path}: expected basic-block index ({e})"
  if id >= blockCount then throw s!"{path}: basic block {id} is out of range (blocks={blockCount})"

private def checkRequiredEdge (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  checkBlockIndex (← field j key path) (joinPath path key) blockCount

private def checkOptionalEdge (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  match optionalField j key with
  | none => throw s!"{path}: missing optional edge field `{key}`"
  | some .null => pure ()
  | some value => checkBlockIndex value (joinPath path key) blockCount

private def validateUnwind (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let kind ← fieldString j "kind" path
  if kind == "Cleanup" then checkRequiredEdge j "target" path blockCount

private def validateTerminatorEdges (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let variant ← fieldString j "variant" path
  match variant with
  | "Goto" => checkRequiredEdge j "target" path blockCount
  | "SwitchInt" =>
    checkRequiredEdge j "otherwise" path blockCount
    let targets ← arrayField j "targets" path
    for (target, index) in targets.toList.zipIdx do
      checkRequiredEdge target "target" s!"{joinPath path "targets"}[{index}]" blockCount
  | "Drop" =>
    checkRequiredEdge j "target" path blockCount
    checkOptionalEdge j "async_drop" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Call" =>
    checkOptionalEdge j "target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Assert" =>
    checkRequiredEdge j "target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Yield" =>
    checkRequiredEdge j "resume" path blockCount
    checkOptionalEdge j "drop" path blockCount
  | "FalseEdge" =>
    checkRequiredEdge j "real_target" path blockCount
    checkRequiredEdge j "imaginary_target" path blockCount
  | "FalseUnwind" =>
    checkRequiredEdge j "real_target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | _ => pure ()

private def validateBody (j : Json) (path : String) : Except String Unit := do
  let locals ← arrayField j "locals" path
  let blocks ← arrayField j "basic_blocks" path
  if locals.isEmpty then throw s!"{joinPath path "locals"}: MIR body must declare the return local"
  if blocks.isEmpty then throw s!"{joinPath path "basic_blocks"}: MIR body must contain a start block"
  let mut index := 0
  for localDecl in locals do
    let id ← fieldNat localDecl "local" s!"{joinPath path "locals"}[{index}]"
    if id != index then throw s!"{joinPath path "locals"}[{index}]: local declarations must be densely ordered"
    index := index + 1
  index := 0
  for block in blocks do
    let blockPath := s!"{joinPath path "basic_blocks"}[{index}]"
    let id ← fieldNat block "block" blockPath
    if id != index then throw s!"{blockPath}: basic blocks must be densely ordered"
    let statements ← arrayField block "statements" blockPath
    for (statement, stmtIndex) in statements.toList.zipIdx do
      let kind ← field statement "kind" s!"{blockPath}.statements[{stmtIndex}]"
      validateMirIndices kind s!"{blockPath}.statements[{stmtIndex}].kind" locals.size
    let termWrapper ← field block "terminator" blockPath
    if termWrapper == .null then throw s!"{blockPath}: missing terminator"
    let term ← field termWrapper "kind" s!"{blockPath}.terminator"
    validateMirIndices term s!"{blockPath}.terminator.kind" locals.size
    validateTerminatorEdges term s!"{blockPath}.terminator.kind" blocks.size
    index := index + 1

private partial def validateAllBodies (j : Json) (path : String) : Except String Unit := do
  if statusOf? j == some "debug_payload" then return
  match j with
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      validateAllBodies value s!"{path}[{index}]"
  | .obj fields =>
    let hasLocals := (j.getObjVal? "locals").isOk
    let hasBlocks := (j.getObjVal? "basic_blocks").isOk
    if hasLocals != hasBlocks then throw s!"{path}: body requires both locals and basic_blocks"
    if hasLocals && hasBlocks then validateBody j path
    for (key, value) in fields.toList do
      validateAllBodies value (joinPath path key)
  | _ => pure ()

private def jsonToNatArray (nodes : Array α) (getId : α → Nat) : Array Nat := nodes.map getId

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

private def validateTaggedNode (node : TaggedNode) (known : List String)
    (path description : String) : Except String Unit := do
  if !known.contains node.tag then
    throw (joinPath path "kind" ++ ": " ++ s!"unrecognized {description} tag `{node.tag}`")
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

private def validateExternAbi (abi : ExternAbi) (path : String) : Except String Unit := do
  validateTaggedNode abi.kind
    ["c", "system", "rust", "rust_call", "rust_cold", "rust_invalid", "rust_preserve_none",
      "rust_tail", "llvm_intrinsic", "custom", "efi_api", "swift", "aapcs",
      "cmse_nonsecure_call", "cmse_nonsecure_entry", "gpu_kernel", "ptx_kernel",
      "avr_interrupt", "avr_non_blocking_interrupt", "msp430_interrupt",
      "riscv_interrupt_machine", "riscv_interrupt_supervisor", "x86_interrupt", "cdecl",
      "stdcall", "fastcall", "thiscall", "vectorcall", "sysv64", "win64"]
    path "extern ABI"
  let hasUnwindTag := ["c", "system", "aapcs", "cdecl", "stdcall", "fastcall", "thiscall", "vectorcall", "sysv64", "win64"].contains abi.kind.tag
  if hasUnwindTag && abi.unwind.isNone then
    throw (joinPath path "unwind" ++ ": " ++ "this extern ABI requires an explicit unwind flag")
  if !hasUnwindTag && abi.unwind.isSome then
    throw (joinPath path "unwind" ++ ": " ++ "extern ABI has an unexpected unwind flag")
  if abi.sourceSpelling.isNone then
    throw (joinPath path "source_spelling" ++ ": " ++ "extern ABI is missing its original spelling")
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

private def validateVirtualIdentity (raw : Json) (types : Array TypeNode)
    (instances : Array InstanceNode) : Except String Unit := do
  for (node, index) in instances.toList.zipIdx do
    if node.kind != .virtualDispatchTarget then continue
    let base := s!"$.instances[{index}]"
    let payload := node.payload
    if (payload.getObjValAs? String "body_status").toOption != some "not_applicable" then
      throw (base ++ ".body_status" ++ ": " ++ "virtual dispatch identity must explicitly have no executable MIR body")
    if node.bodyId.isSome then
      throw (base ++ ".body" ++ ": " ++ "virtual dispatch identity cannot carry a fabricated MIR body")
    let kind := (payload.getObjVal? "instance_kind").toOption.getD .null
    if (kind.getObjValAs? String "kind").toOption != some "virtual" then
      throw (base ++ ".instance_kind.kind" ++ ": " ++ "virtual dispatch target must retain rustc InstanceKind::Virtual")
    if (kind.getObjVal? "def_id").toOption != (payload.getObjVal? "def_id").toOption then
      throw (base ++ ".instance_kind.def_id" ++ ": " ++ "virtual InstanceKind DefId disagrees with catalog DefId")
    if (kind.getObjVal? "dispatch_slot").toOption != (payload.getObjVal? "dispatch_slot").toOption then
      throw (base ++ ".instance_kind.dispatch_slot" ++ ": " ++ "virtual InstanceKind slot disagrees with catalog slot")
    let identity := (payload.getObjVal? "virtual_identity").toOption.getD .null
    let functionType := (identity.getObjVal? "function_type").toOption.getD .null
    let typeId := functionType.getNat?.toOption
    match typeId with
    | none => throw (base ++ ".virtual_identity.function_type" ++ ": " ++ "virtual method identity is missing its compiler function type")
    | some id =>
      let typeMatches := types.filter (·.id == id)
      if typeMatches.size != 1 then
        throw (base ++ ".virtual_identity.function_type" ++ ": " ++ "virtual method identity references a missing or ambiguous type")
      else if let some ty := typeMatches[0]? then
        if ty.shapeKind != .functionPointer && ty.shapeKind != .functionDefinition then
          throw (base ++ ".virtual_identity.function_type" ++ ": " ++ "virtual method identity type is not a compiler function value")
    let abi := (identity.getObjVal? "fn_abi").toOption.getD .null
    let abiValue := some abi
    let catalog := ((raw.getObjVal? "compiler_instance_abis").bind Json.getArr?).toOption.getD #[]
    let abiRows := catalog.filter fun row =>
      (row.getObjValAs? Nat "instance_id").toOption == some node.id
    if abiRows.size != 1 then
      throw (base ++ ".virtual_identity.fn_abi" ++ ": " ++ "virtual identity must match one exact full-instance FnAbi query")
    else if let some row := abiRows[0]? then
      let query := (row.getObjVal? "abi_query").toOption.getD .null
      if abiValue != some query then
        throw (base ++ ".virtual_identity.fn_abi" ++ ": " ++ "virtual identity FnAbi disagrees with the exact full-instance FnAbi query")
  return ()

private def validateExtraSemantic (raw : Json) (types : Array TypeNode) (allocations : Array AllocationNode)
    (instances : Array InstanceNode) (functionAbis : Array FunctionAbi) (bodies : Array Body)
    (layouts : Array Layout) : Except String Unit := do
  validateVirtualIdentity raw types instances
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
    match node.signature with
    | some signature =>
      validateTaggedNode signature.safety ["safe", "unsafe"]
        s!"types[{node.id}].shape.signature.safety" "function safety"
      validateExternAbi signature.abi s!"types[{node.id}].shape.signature.abi"
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
      match node.bodyInstantiation with
      | none => throw (s!"instances[{node.id}].body_instantiation" ++ ": " ++ "instance body is missing substitution/normalization evidence")
      | some detail =>

        if detail.tag != "substituted_and_normalized" then
          throw (s!"instances[{node.id}].body_instantiation.kind" ++ ": " ++ s!"unsupported instance body transformation `{detail.tag}`")
      if node.bodyTemplateIsPolymorphic.isNone then
        throw (s!"instances[{node.id}].body_template_is_polymorphic" ++ ": " ++ "instance lacks polymorphism metadata for its body template")
      if node.instanceArgsAreMonomorphic != some true then
        throw (s!"instances[{node.id}].instance_args_are_monomorphic" ++ ": " ++ "instance arguments are not known to be monomorphic")
    | .intrinsicDispatch =>
      let base := s!"instances[{node.id}]"
      if node.bodyId.isSome then
        throw (joinPath base "body" ++ ": " ++ "intrinsic dispatch identity cannot carry fabricated MIR")
      let instanceKind := (node.payload.getObjVal? "instance_kind").toOption.getD .null
      let tag := (instanceKind.getObjValAs? String "kind").toOption
      if tag != some "intrinsic" && tag != some "llvm_intrinsic" then
        throw (joinPath base "instance_kind.kind" ++ ": " ++ "intrinsic dispatch requires exact rustc Intrinsic or LlvmIntrinsic identity")
      let topDefId := node.definitionId
      let nestedDefIdJson := (instanceKind.getObjVal? "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind (·.getNat?.toOption)
      if topDefId.isNone then
        throw (joinPath base "def_id" ++ ": " ++ "intrinsic dispatch requires an exact top-level rustc DefId")
      if nestedDefId.isNone then
        throw (joinPath base "instance_kind.def_id" ++ ": " ++ "intrinsic dispatch requires an exact nested rustc DefId")
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        throw (joinPath base "instance_kind.def_id" ++ ": " ++ "intrinsic identity DefId disagrees with its instance record")
    | .foreignItemNoMir =>
      let base := s!"instances[{node.id}]"
      if node.bodyId.isSome then
        throw (joinPath base "body" ++ ": " ++ "foreign declaration cannot carry fabricated MIR")
      if (node.payload.getObjValAs? Bool "foreign_item").toOption != some true then
        throw (joinPath base "foreign_item" ++ ": " ++ "no-MIR foreign dispatch requires exact rustc is_foreign_item=true evidence")
      let symbol := (node.payload.getObjVal? "symbol_name").toOption.getD .null
      if (symbol.getStr?.toOption.getD "").isEmpty then
        throw (joinPath base "symbol_name" ++ ": " ++ "no-MIR foreign dispatch requires an exact nonempty rustc symbol name")
      let instanceKind := (node.payload.getObjVal? "instance_kind").toOption.getD .null
      if (instanceKind.getObjValAs? String "kind").toOption != some "item" then
        throw (joinPath base "instance_kind.kind" ++ ": " ++ "foreign dispatch requires exact rustc Item identity")
      let topDefId := node.definitionId
      let nestedDefIdJson := (instanceKind.getObjVal? "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind (·.getNat?.toOption)
      if topDefId.isNone then
        throw (joinPath base "def_id" ++ ": " ++ "foreign dispatch requires an exact top-level rustc DefId")
      if nestedDefId.isNone then
        throw (joinPath base "instance_kind.def_id" ++ ": " ++ "foreign dispatch requires an exact nested rustc DefId")
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        throw (joinPath base "instance_kind.def_id" ++ ": " ++ "foreign identity DefId disagrees with its instance record")
    | .virtualDispatchTarget => pure ()
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

private def validateSelectedScope (scope : SelectedScope) (_bodies : Array Body)
    (instances : Array InstanceNode) (bodyRoots : Array BodyRoot) : Except String Unit := do
  if scope.kind != "rooted_structural_closure" then
    throw ("$.selected_scope.kind" ++ ": " ++ s!"unrecognized selected-scope kind `{scope.kind}`")
  if scope.semantics != "structural_export_closure_only" then
    throw ("$.selected_scope.semantics" ++ ": " ++ s!"unrecognized scope guarantee `{scope.semantics}`")
  if scope.roots.isEmpty then throw ("$.selected_scope.roots" ++ ": " ++ "selected structural closure has no root")
  for (root, index) in scope.roots.toList.zipIdx do
    let resolvedBody := bodyRoots.any fun body =>
      body.definitionId == some root.definitionId && body.defPath == root.defPath
    let resolvedInstance := instances.any fun inst =>
      inst.definitionId == some root.definitionId && inst.defPath == some root.defPath
    if !resolvedBody && !resolvedInstance then
      throw (s!"$.selected_scope.roots[{index}]" ++ ": " ++ "selected DefId and path do not resolve to an emitted body or instance")
  return ()

private partial def collectGraphReferencesInto (j : Json)
    (result : Array (String × Nat)) (metadata : Bool := false) : Array (String × Nat) := Id.run do
  match j with
  | .obj fields =>
    if statusOf? j == some "debug_payload" then return result
    let mut result := result
    let metadata := metadata || (j.getObjValAs? String "kind").toOption == some "function_definition"
    for (key, value) in fields.toList do
      if ["normalization_template", "compiler_facts", "constructor_identity"].contains key then continue
      let childMetadata := metadata || ["constant_query_context", "inlined"].contains key
      if let some reference := referenceField j key value then
        match reference with
        | .typeRef id => result := result.push ("type_id", id)
        | .allocationRef id => result := result.push ("allocation_id", id)
        | .instanceRef id => result := result.push (if childMetadata then "metadata_instance_id" else "instance_id", id)
        | _ => pure ()
      if key == "entry_instance" then
        if let .ok id := value.getNat? then result := result.push ("instance_id", id)
      if key == "body" then
        if let .ok id := value.getNat? then
          result := result.push (if childMetadata then "metadata_body_id" else "body_id", id)
      if key == "elements" && (j.getObjValAs? String "kind").toOption == some "tuple" then
        for child in value.getArr?.toOption.getD #[] do
          if let .ok id := child.getNat? then result := result.push ("type_id", id)
      result := collectGraphReferencesInto value result childMetadata
    return result
  | .arr values =>
    let mut result := result
    for value in values do result := collectGraphReferencesInto value result metadata
    return result
  | _ => return result

private def collectGraphReferences (j : Json) (metadata : Bool := false) : Array (String × Nat) :=
  collectGraphReferencesInto j #[] metadata

private def rawArray (j : Json) (key : String) : Array Json :=
  ((j.getObjVal? key).bind Json.getArr?).toOption.getD #[]

private partial def collectThreadLocalRefsInto (j : Json) (path : String)
    (found : Array (String × Json)) : Array (String × Json) := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return found
    let mut found := if (j.getObjValAs? String "kind").toOption == some "ThreadLocalRef" then found.push ⟨path,j⟩ else found
    for (key, value) in fields.toList do
      found := collectThreadLocalRefsInto value (joinPath path key) found
    return found
  | .arr values =>
    let mut found := found
    let mut index := 0
    for value in values do
      found := collectThreadLocalRefsInto value s!"{path}[{index}]" found
      index := index + 1
    return found
  | _ => return found

private def collectThreadLocalRefs (j : Json) (path : String) : Array (String × Json) :=
  collectThreadLocalRefsInto j path #[]

private structure RequiredStructuralDependencies where
  typeIds : Array Nat := #[]
  instanceIds : Array Nat := #[]
  allocationIds : Array Nat := #[]
  threadLocalRefs : Array (String × Json) := #[]

private def requiredStructuralDependencies (j : Json) (includeAllBodies : Bool := false) : RequiredStructuralDependencies := Id.run do
  let roots := match optionalField j "selected_scope" with
    | some scope => rawArray scope "roots"
    | none => #[]
  if roots.isEmpty && !includeAllBodies then return {}
  let bodyRows := rawArray j "bodies"
  let instanceRows := rawArray j "instances"
  let allocationRows := rawArray j "allocations"
  let typeRows := rawArray j "types"
  let rootRows := rawArray j "body_roots"
  let selected := if roots.isEmpty then rootRows else rootRows.filter fun body =>
    roots.any fun root =>
      optionalField root "def_id" == optionalField body "def_id" &&
      optionalField root "def_path" == optionalField body "def_path"
  let mut pending : Array (String × Nat) := #[]
  for root in selected do pending := pending ++ collectGraphReferences root
  let mut requiredTypes := #[]
  let mut requiredInstances := #[]
  let mut requiredAllocations := #[]
  let mut requiredTls := #[]
  let mut visited : Std.HashSet (String × Nat) := {}
  while !pending.isEmpty do
    let current := pending
    pending := #[]
    for (kind, id) in current do
      if visited.contains (kind, id) then continue
      visited := visited.insert (kind, id)
      if kind == "type_id" then
        requiredTypes := requiredTypes.push id
        if let some row := typeRows[id]? then
          if let some shape := optionalField row "shape" then
            pending := pending ++ collectGraphReferences shape true
      else if kind == "allocation_id" then
        requiredAllocations := requiredAllocations.push id
        if let some row := allocationRows[id]? then
          pending := pending ++ collectGraphReferences row
      else if kind == "instance_id" || kind == "metadata_instance_id" then
        let metadata := kind == "metadata_instance_id"
        if !metadata then requiredInstances := requiredInstances.push id
        if let some row := instanceRows[id]? then
          pending := pending ++ collectGraphReferences row metadata
      else if kind == "body_id" || kind == "metadata_body_id" then
        let metadata := kind == "metadata_body_id"
        if let some row := bodyRows[id]? then
          if !metadata then
            requiredTls := requiredTls ++ collectThreadLocalRefs row s!"$.bodies[{id}]"
          pending := pending ++ collectGraphReferences row metadata
  return ⟨requiredTypes, requiredInstances, requiredAllocations, requiredTls⟩

/-- Symbol-only entries close compiler identity references but carry no MIR.
Their absence of a body is harmless while they are unused catalog rows, but
any row reached from a selected root or executable graph is an unresolved
structural dependency. -/
private def validateRequiredIdentityOnlyInstance (instances : Array InstanceNode)
    (requiredIds : Array Nat) : Except String Unit := do
  for (node, index) in instances.toList.zipIdx do
    if requiredIds.contains node.id && node.kind == .identityOnly then
      throw (s!"$.instances[{index}].kind" ++ ": " ++ "selected execution depends on a symbol identity that has no imported MIR body")
  return ()

private def validateThreadLocalShape (references : Array (String × Json)) : Except String Unit := do
  for (path, value) in references do
    let definition := (value.getObjVal? "def_id").toOption
    match definition with
    | none => throw (joinPath path "def_id" ++ ": " ++ "supported ThreadLocalRef is missing its exact compiler DefId")
    | some defId =>
      for key in ["crate", "index"] do
        if ((defId.getObjVal? key).bind Json.getNat?).toOption.isNone then
          throw (joinPath (joinPath path "def_id") key ++ ": " ++ "ThreadLocalRef DefId component must be an unsigned integer")
    let info := (value.getObjVal? "global_info").toOption
    match info with
    | none => throw (joinPath path "global_info" ++ ": " ++ "supported ThreadLocalRef is missing static compiler query evidence")
    | some info =>
      if (info.getObjValAs? Bool "is_static").toOption != some true then
        throw (joinPath (joinPath path "global_info") "is_static" ++ ": " ++ "ThreadLocalRef DefId is not confirmed as a static")
      if (info.getObjValAs? Bool "thread_local").toOption != some true then
        throw (joinPath (joinPath path "global_info") "thread_local" ++ ": " ++ "ThreadLocalRef DefId is not confirmed as thread-local")
      if (info.getObjValAs? Bool "is_foreign_item").toOption.isNone then
        throw (joinPath (joinPath path "global_info") "is_foreign_item" ++ ": " ++ "ThreadLocalRef static query lacks its foreign-item predicate")
    let initializer := (value.getObjVal? "initializer").toOption
    match initializer with
    | none => throw (joinPath path "initializer" ++ ": " ++ "supported ThreadLocalRef is missing exact initializer query evidence")
    | some initializer =>
      let initializerPath := joinPath path "initializer"
      let allocation := (initializer.getObjVal? "allocation").toOption
      match allocation with
      | none => throw (joinPath initializerPath "allocation" ++ ": " ++ "supported TLS initializer is missing its allocation image")
      | some allocation =>
        let allocationPath := joinPath initializerPath "allocation"
        match parseAllocationMemory allocation allocationPath with
        | .error reason => throw (allocationPath ++ ": " ++ reason)
        | .ok memory =>
          if let some info := info then
            match (info.getObjVal? "size_bytes").bind Json.getNat? with
            | .ok size => if size != memory.sizeBytes then
                throw (joinPath allocationPath "size_bytes" ++ ": " ++ "TLS initializer size disagrees with static compiler query")
            | .error _ => throw (joinPath (joinPath path "global_info") "size_bytes" ++ ": " ++ "TLS static query is missing its allocation size")
            match (info.getObjVal? "align_bytes").bind Json.getNat? with
            | .ok align => if align != memory.alignBytes then
                throw (joinPath allocationPath "align_bytes" ++ ": " ++ "TLS initializer alignment disagrees with static compiler query")
            | .error _ => throw (joinPath (joinPath path "global_info") "align_bytes" ++ ": " ++ "TLS static query is missing its allocation alignment")
  return ()

private def jsonAtPathSegment (j : Json) (segment : String) : Option Json := Id.run do
  match segment.splitOn "[" with
  | [key] => return (j.getObjVal? key).toOption
  | [key, suffix] =>
    let pieces := suffix.splitOn "]"
    let [indexText, ""] := pieces | return none
    let .ok index := decimalNat indexText segment | return none
    let some arrayJson := (j.getObjVal? key).toOption | return none
    let some values := arrayJson.getArr?.toOption | return none
    return values[index]?
  | _ => return none

def jsonAtPath (j : Json) (path : String) : Option Json := Id.run do
  unless path.startsWith "$." do return none
  let segments := (path.drop 2).toString.splitOn "."
  let mut current := some j
  for segment in segments do
    current := current.bind (fun value => jsonAtPathSegment value segment)
  return current

private def jsonTypeId? (j : Json) : Option Nat :=
  j.getNat?.toOption

private def dynamicPredicateArray? (j : Json) (typeId : Nat) : Option (Array Json) := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    ((ty.getObjValAs? Nat "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := (ty.getObjVal? "shape").toOption | return none
  unless ((shape.getObjValAs? String "kind").toOption == some "dynamic_trait_object") do return none
  return ((shape.getObjVal? "predicates").bind Json.getArr?).toOption

private def compilerBuiltinDerefType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    ((ty.getObjValAs? Nat "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some facts := (ty.getObjVal? "compiler_facts").toOption | return none
  let some queries := (facts.getObjVal? "type_queries").toOption | return none
  let some query := (queries.getObjVal? "builtin_deref_explicit").toOption | return none
  return jsonTypeId? query

private def exactLockstepTails? (j : Json) (source target : Nat) : Option Json := Id.run do
  let some rows := (((j.getObjVal? "compiler_cast_queries").bind Json.getArr?).toOption) | return none
  let matching := rows.filter fun row =>
    ((row.getObjValAs? String "query_kind").toOption == some "lockstep_tails") &&
    ((row.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
    ((row.getObjVal? "input_source").toOption.bind jsonTypeId? == some source) &&
    ((row.getObjVal? "input_target").toOption.bind jsonTypeId? == some target)
  unless matching.size == 1 do return none
  return matching[0]?

private def castOperandTypeId? (node : Json) : Option Nat := Id.run do
  let some operand := (node.getObjVal? "operand").toOption | return none
  let some operandKind := ((operand.getObjVal? "kind").bind Json.getStr?).toOption | return none
  if operandKind == "Copy" || operandKind == "Move" then
    let some place := (operand.getObjVal? "place").toOption | return none
    let some ty := (place.getObjVal? "type").toOption | return none
    return jsonTypeId? ty
  else if operandKind == "Constant" then
    let some constant := (operand.getObjVal? "constant").toOption | return none
    let some ty := (constant.getObjVal? "type").toOption | return none
    return jsonTypeId? ty
  else return none

/-- A dynamic-to-dynamic Unsize is represented by the runtime source-vtable
operation. Bind its descriptor to the Cast's complete types, both exact
lockstep queries, and the compiler's fully-monomorphized supertrait-slot row.
This validates evidence identity only; the runtime still obtains the table
from the actual source operand. -/
private def castUnsizingPointeeType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty => (ty.getObjValAs? Nat "type_id").toOption == some typeId
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := (ty.getObjVal? "shape").toOption | return none
  let some kind := (shape.getObjValAs? String "kind").toOption | return none
  if kind == "reference" || kind == "raw_pointer" then
    return (shape.getObjVal? "pointee").toOption.bind jsonTypeId?
  else
    return some typeId

private def exactDynamicVtableUpcast? (j node descriptor : Json) : Bool := Id.run do
  unless ((node.getObjValAs? String "kind").toOption == some "Cast") do return false
  let some castKind := (node.getObjVal? "cast_kind").toOption | return false
  unless ((castKind.getObjValAs? String "kind").toOption == some "PointerCoercion") do return false
  let some coercion := (castKind.getObjVal? "coercion").toOption | return false
  unless (coercion.getObjValAs? String "kind").toOption == some "Unsize" do return false
  unless ((descriptor.getObjValAs? String "kind").toOption == some "dynamic_vtable_upcast") do return false
  let some sourceType := (descriptor.getObjVal? "source_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  let some targetType := (descriptor.getObjVal? "target_type").toOption | return false
  let some targetTypeId := jsonTypeId? targetType | return false
  unless castOperandTypeId? node == some sourceTypeId do return false
  unless ((node.getObjVal? "target_type").toOption.bind jsonTypeId?) == some targetTypeId do return false

  let some sourcePointee := (descriptor.getObjVal? "source_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointee := (descriptor.getObjVal? "target_pointee_type").toOption | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless castUnsizingPointeeType? j sourceTypeId == some sourcePointeeId &&
      castUnsizingPointeeType? j targetTypeId == some targetPointeeId do return false

  let some fullLockstep := exactLockstepTails? j sourceTypeId targetTypeId | return false
  let some fullSourceTail := ((fullLockstep.getObjVal? "source_tail").toOption.bind jsonTypeId?) | return false
  let some fullTargetTail := ((fullLockstep.getObjVal? "target_tail").toOption.bind jsonTypeId?) | return false
  unless fullSourceTail == sourceTypeId && fullTargetTail == targetTypeId do return false

  let some sourcePointeeLockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some sourceTail := (descriptor.getObjVal? "source_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTail := (descriptor.getObjVal? "target_tail_type").toOption | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  unless ((sourcePointeeLockstep.getObjVal? "source_tail").toOption.bind jsonTypeId?) == some sourceTailId &&
      ((sourcePointeeLockstep.getObjVal? "target_tail").toOption.bind jsonTypeId?) == some targetTailId do return false
  unless (dynamicPredicateArray? j sourceTailId).isSome &&
      (dynamicPredicateArray? j targetTailId).isSome do return false

  unless (descriptor.getObjValAs? String "runtime_vtable").toOption ==
      some "source_operand_metadata" do return false
  let some embeddedQuery := (descriptor.getObjVal? "supertrait_slot_query").toOption | return false
  unless ((embeddedQuery.getObjValAs? String "query_kind").toOption == some "supertrait_slot") &&
      ((embeddedQuery.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
      ((embeddedQuery.getObjVal? "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
      ((embeddedQuery.getObjVal? "input_target").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := (((j.getObjVal? "compiler_cast_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    ((row.getObjValAs? String "query_kind").toOption == some "supertrait_slot") &&
    ((row.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
    ((row.getObjVal? "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
    ((row.getObjVal? "input_target").toOption.bind jsonTypeId? == some targetTailId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless (match row.getObjVal? "value" with
    | .ok .null => true
    | .ok value => (value.getNat?).isOk
    | .error _ => false) do return false
  return true

private partial def malformedDynamicVtableUpcastAux (root current : Json) (path : String) : Option String := do
  match current with
  | .obj fields =>
    if (current.getObjValAs? String "kind").toOption == some "Cast" then
      if let some descriptor := (current.getObjVal? "vtable_allocation").toOption then
        if (descriptor.getObjValAs? String "kind").toOption == some "dynamic_vtable_upcast" &&
            !exactDynamicVtableUpcast? root current descriptor then
          return joinPath path "vtable_allocation"
    for (key, value) in fields.toList do
      if let some bad := malformedDynamicVtableUpcastAux root value (joinPath path key) then return bad
    none
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      if let some bad := malformedDynamicVtableUpcastAux root value s!"{path}[{index}]" then return bad
    none
  | _ => none

private def malformedDynamicVtableUpcast? (j : Json) : Option String :=
  malformedDynamicVtableUpcastAux j j "$"

private def parseTypeArray (values : Array Json) : Except String (Array TypeNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseTypeNode value s!"$.types[{index}]")
    index := index + 1
  pure result

private def parseAllocationArray (values : Array Json) : Except String (Array AllocationNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseAllocation value s!"$.allocations[{index}]")
    index := index + 1
  pure result

private def parseInstanceArray (values : Array Json) : Except String (Array InstanceNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseInstance value s!"$.instances[{index}]")
    index := index + 1
  pure result

private def parseBodyArray (values : Array Json) : Except String (Array Body) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    let fallback := match optionalField value "def_path" with
      | some (.str name) => name
      | _ => s!"body[{index}]"
    result := result.push (← parseBody value s!"$.bodies[{index}]" fallback)
    index := index + 1
  pure result

private def parseDocument (input : Json) (profile : Options := {}) : Except String ExecutionInput := do
  let j := input
  let traversal := input
  if (← fieldString j "schema" "$") != expectedSchema then
    throw s!"$.schema: expected `{expectedSchema}`"
  if (← fieldNat j "schema_version" "$") != expectedSchemaVersion then
    throw s!"$.schema_version: unsupported schema version"
  if hasField j "shared_payloads" then throw "$.shared_payloads: generic payload graphs are not part of this schema"
  if let some path := profileit "decoder.dynamic_vtable_scan" profile fun _ =>
      malformedDynamicVtableUpcast? traversal then
    throw s!"{path}: supported dynamic vtable upcast lacks matching compiler cast evidence"
  let producerJson ← field j "producer" "$"
  let producer : Producer := {
    miriCommit := ← fieldString producerJson "miri_commit" "$.producer"
    rustcCommit := ← fieldString producerJson "rustc_commit" "$.producer"
    rustcVersion := ← fieldString producerJson "rustc_version" "$.producer"
    targetTriple := ← fieldString producerJson "target_triple" "$.producer"
  }
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  let predicates ← ((← arrayField j "predicates" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseVtablePredicate value s!"$.predicates[{index}]").map List.toArray
  let mut predicateIdentities : Std.HashMap Nat (Array VtablePredicate) := {}
  for (predicate, index) in predicates.toList.zipIdx do
    let previous := predicateIdentities.getD predicate.definitionId #[]
    if previous.any (fun other => decide (other.kind = predicate.kind ∧ other.genericArgs = predicate.genericArgs ∧
        other.boundVariables = predicate.boundVariables ∧ other.projectionTerm = predicate.projectionTerm)) then
      throw s!"$.predicates[{index}]: duplicate compiler predicate identity"
    predicateIdentities := predicateIdentities.insert predicate.definitionId (previous.push predicate)
  let compilerPredicates ← (← arrayField j "compiler_predicate_queries" "$").mapM decodeCompilerPredicateEvidence
  unless compilerPredicates.size == predicates.size do
    throw "$.compiler_predicate_queries: predicate query and definition tables differ in size"
  for (query, index) in compilerPredicates.toList.zipIdx do
    unless query.id == index && query.original == index do
      throw s!"$.compiler_predicate_queries[{index}]: predicate query identity mismatch"
    let some definition := predicates[index]? | throw "compiler predicate table index invariant"
    unless query.autoTrait == (definition.kind == .autoTrait) do
      throw s!"$.compiler_predicate_queries[{index}]: auto-trait query disagrees with predicate definition"
    if let some normalized := query.normalizedId then
      unless normalized < predicates.size do
        throw s!"$.compiler_predicate_queries[{index}]: dangling normalized predicate reference {normalized}"
  let definitions ← ((← arrayField j "definitions" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseDefinitionId value s!"$.definitions[{index}]").map List.toArray
  let mut definitionKeys : Std.HashSet (Nat × Nat) := {}
  for (definition, index) in definitions.toList.zipIdx do
    let key := (definition.crateIndex, definition.index)
    if definitionKeys.contains key then throw s!"$.definitions[{index}]: duplicate compiler definition identity"
    definitionKeys := definitionKeys.insert key
  let typeConstants ← ((← arrayField j "type_constants" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    TypeConstCodec.decode value s!"$.type_constants[{index}]").map List.toArray
  let mut constantValues : Array MIR.TypeConst := #[]
  for (constant, index) in typeConstants.toList.zipIdx do
    if constantValues.contains constant then
      throw s!"$.type_constants[{index}]: duplicate compiler type-constant identity"
    constantValues := constantValues.push constant
  let spans ← ((← arrayField j "spans" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseSourceSpan value s!"$.spans[{index}]").map List.toArray
  let layouts ← ((← arrayField j "layouts" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseLayout value s!"$.layouts[{index}]").map List.toArray
  let functionAbis ← ((← arrayField j "fn_abis" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseFunctionAbi value s!"$.fn_abis[{index}]").map List.toArray
  let typesJson ← arrayField j "types" "$"
  if typesJson.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  let types ← profileit "decoder.types" profile fun _ => parseTypeArray typesJson
  let allocationsJson ← arrayField j "allocations" "$"
  let allocations ← profileit "decoder.allocations" profile fun _ => parseAllocationArray allocationsJson
  let compilerAllocIdWorld ← profileit "decoder.compiler_alloc_id_world" profile fun _ => do
    match optionalJson j "compiler_alloc_id_world" with
    | none => pure none
    | some value => pure (some (← parseCompilerAllocIdWorld value allocations))
  let instancesJson ← arrayField j "instances" "$"
  let instances ← profileit "decoder.instances" profile fun _ => parseInstanceArray instancesJson
  let mut instanceIdentities : Std.HashMap Nat (Array InstanceNode) := {}
  for (node, index) in instances.toList.zipIdx do
    let definition := node.instanceKind.defId
    let previous := instanceIdentities.getD definition #[]
    if previous.any (fun other => decide (other.instanceKind = node.instanceKind ∧ other.genericArgs = node.genericArgs)) then
      throw s!"$.instances[{index}]: duplicate compiler instance identity"
    instanceIdentities := instanceIdentities.insert definition (previous.push node)
  let selectedScope ← match optionalJson j "selected_scope" with
    | none => pure none
    | some value =>
      for legacyField in ["unresolved_obligations", "retained_catalog_obligations"] do
        if hasField value legacyField then
          throw s!"$.selected_scope.{legacyField}: obsolete failed-input field"
      pure (some (← parseSelectedScope value "$.selected_scope"))
  let compilerAbiLayoutSchema ← fieldString j "compiler_abi_layout_schema" "$"
  unless compilerAbiLayoutSchema == expectedCompilerAbiLayoutSchema do
    throw s!"$.compiler_abi_layout_schema: unsupported schema `{compilerAbiLayoutSchema}`"
  let bodiesJson ← arrayField j "bodies" "$"
  if bodiesJson.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  let bodies ← profileit "decoder.bodies" profile fun _ => parseBodyArray bodiesJson
  let bodyRoots ← ((← arrayField j "body_roots" "$").toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseBodyRoot value s!"$.body_roots[{index}]").map List.toArray
  let typeIds := jsonToNatArray types (·.id)
  let allocationIds := jsonToNatArray allocations (·.id)
  let instanceIds := jsonToNatArray instances (·.id)
  profileit "decoder.validate_dense_type_ids" profile fun _ => validateDense typeIds "type IDs"
  profileit "decoder.validate_dense_allocation_ids" profile fun _ => validateDense allocationIds "allocation IDs"
  profileit "decoder.validate_dense_instance_ids" profile fun _ => validateDense instanceIds "instance IDs"
  profileit "decoder.validate_all_bodies" profile fun _ => validateAllBodies traversal "$"
  profileit "decoder.validate_references" profile fun _ =>
    validateReferences traversal "$" types.size allocations.size instances.size layouts.size functionAbis.size spans.size definitions.size typeConstants.size bodies.size predicates.size
  profileit "decoder.extra_semantic_validation" profile fun _ =>
    validateExtraSemantic j types allocations instances functionAbis bodies layouts
  let requiredDependencies := profileit "decoder.required_dependencies" profile fun _ =>
    requiredStructuralDependencies j compilerAllocIdWorld.isSome
  profileit "decoder.required_instance_validation" profile fun _ =>
    validateRequiredIdentityOnlyInstance instances requiredDependencies.instanceIds
  profileit "decoder.thread_local_validation" profile fun _ =>
    validateThreadLocalShape requiredDependencies.threadLocalRefs
  match selectedScope with
  | some scope => profileit "decoder.selected_scope_validation" profile fun _ =>
      validateSelectedScope scope bodies instances bodyRoots
  | none => pure ()
  let runtimeTargetDataLayout ← match optionalJson j "runtime_target_data_layout" with
    | none => pure none
    | some evidence => pure (some ({
        payload := evidence
      } : TargetDataLayoutEvidence))
  let core : ImportDocument := {
    compilerPredicates := compilerPredicates
    compilerAbiLayoutSchema := some compilerAbiLayoutSchema
    producer := producer
    runtimeTargetDataLayout := runtimeTargetDataLayout
    predicates := predicates
    definitions := definitions
    typeConstants := typeConstants
    layouts := layouts
    spans := spans
    types := types
    allocations := allocations
    compilerAllocIdWorld := compilerAllocIdWorld
    instances := instances
    selectedScope := selectedScope
    functionAbis := functionAbis
    bodyRoots := bodyRoots
    bodies := bodies
    raw := j
  }
  validatePrimaryTables core
  pure ⟨core⟩

def decodeJsonProfiled (text : String) (profile : Options) : Except String ExecutionInput := do
  let json ← profileit "decoder.json_parse" profile fun _ => Json.parse text
  profileit "decoder.document" profile fun _ => parseDocument json profile

def decodeJson (text : String) : Except String ExecutionInput :=
  decodeJsonProfiled text {}

def decodeFile (path : System.FilePath) : IO (Except String ExecutionInput) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Typed metadata entrypoints for compiler-query adapters. -/
def decodeAllocationMemoryEvidence (j : Json) : Except String AllocationMemory :=
  parseAllocationMemory j "$allocation"


end Miri.Input
