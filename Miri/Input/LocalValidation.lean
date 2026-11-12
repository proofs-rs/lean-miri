import Miri.Input.Model

namespace Miri.Input.LocalValidation
private def joinPath (path key : String) : String := path ++ "." ++ key

def validatePrimitiveLayout (primitive : PrimitiveLayout) (path : String) : Except String Unit := do
  match primitive.kind with
  | .integer =>
    if primitive.integerKind.isNone || primitive.signed.isNone then
      throw (path ++ ": " ++ "integer primitive layout is missing integer kind or signedness")
  | .float =>
    if primitive.floatKind.isNone then throw (path ++ ": " ++ "float primitive layout is missing float kind")
  | .pointer =>
    if primitive.addressSpace.isNone then throw (path ++ ": " ++ "pointer primitive layout is missing address space")
  return ()

def validateScalarLayout (scalar : ScalarLayout) (path : String) : Except String Unit := do
  validatePrimitiveLayout scalar.primitive (joinPath path "primitive")
  match scalar.kind with
  | .initialized =>
    if scalar.validRange.isNone then throw (path ++ ": " ++ "initialized scalar layout is missing its valid range")
  | .union => pure ()
  return ()

def validateBackendRepr (repr : BackendRepr) (path : String) : Except String Unit := do
  for (key, scalar) in [("scalar", repr.scalar), ("first", repr.first), ("second", repr.second), ("element", repr.element)] do
    match scalar with
    | some value => validateScalarLayout value (joinPath path key)
    | none => pure ()
  return ()

def validateCanonicalAbi (abi : CanonicalAbi) (path : String) : Except String Unit := do
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

def validateAbiRegister (reg : AbiRegister) (path : String) : Except String Unit := do
  match reg.kind with
  | .vector =>
    match reg.hintElement with
    | none => throw (joinPath path "kind.hint_element" ++ ": " ++ "vector ABI register is missing its element hint")
    | some _ => pure ()
  | _ => pure ()
  return ()

def validateAbiPassMode (mode : AbiPassMode) (path : String) : Except String Unit := do
  match mode.castTarget with
  | some target =>
    for (register, index) in target.prefixRegisters.toList.zipIdx do
      validateAbiRegister register s!"{path}.target.prefix_registers[{index}]"
    validateAbiRegister target.restRegister (joinPath path "target.rest_register")
  | none => pure ()
  return ()

def validateAllocationMemory (memory : AllocationMemory) (path : String) : Except String Unit := do
  match memory.mutability with
  | .mutable | .immutable => pure ()
  if memory.alignBytes == 0 then throw (joinPath path "align_bytes" ++ ": " ++ "allocation alignment must be nonzero")
  return ()

def validateTagEncoding (encoding : TagEncoding) (path : String) : Except String Unit := do
  match encoding.kind with
  | .direct => pure ()
  | .niche =>
    if encoding.untaggedVariant.isNone || encoding.nicheVariants.isNone || encoding.nicheStart.isNone then
      throw (path ++ ": " ++ "niche tag encoding is missing its structured variant range or niche start")
    match encoding.nicheVariants with
    | some (first, last) => if last < first then throw (joinPath path "niche_variants" ++ ": " ++ "inclusive niche range has its end before its start")
    | none => pure ()
  return ()

def validatePromotedBody (promoted : Array PromotedBody) (path : String) : Except String Unit := do
  for entry in promoted do
    if entry.bodyId.isNone then
      throw (s!"{path}[{entry.index}]" ++ ": " ++ "promoted MIR body is absent; cannot import it as typed MIR")
  return ()

def validateType (node : TypeNode) : Except String Unit := do
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
  match node.shape with
  | .array _ _ constructor =>
    unless constructor.count < 2^64 do throw s!"types[{node.id}].shape.constructor.count: array count exceeds u64"
  | _ => pure ()

def validateAllocation (node : AllocationNode) : Except String Unit := do
  let allocPath := s!"allocations[{node.id}]"
  match node.kind, node.data with
  | .memory, some (.memory memory) =>
    validateAllocationMemory memory allocPath
  | .function, some (.function _) => pure ()
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

def validateInstance (node : InstanceNode) : Except String Unit := do
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
    if node.virtualIdentity.isNone then
      throw s!"instances[{node.id}].virtual_identity: virtual identity lacks its compiler function type and ABI"
  | .identityOnly =>
    if node.bodyId.isSome then
      throw (s!"instances[{node.id}].body" ++ ": " ++ "symbol identity catalog row must not provide an executable MIR body")
  validatePromotedBody node.promotedBodies s!"instances[{node.id}].promoted_bodies"

def validateFunctionAbi (abi : FunctionAbi) (path : String) : Except String Unit := do
  validateCanonicalAbi abi.callingConvention (path ++ ".calling_convention")
  for (arg, index) in (abi.arguments.push abi.returnValue).toList.zipIdx do
    validateAbiPassMode arg.mode s!"{path}.arguments[{index}].mode"

def validateLayout (layout : Layout) (path : String) : Except String Unit := do
  let constructors := #[layout.tupleType.isSome, layout.unionType.isSome,
    layout.structType.isSome, layout.patternType.isSome, layout.sequenceType.isSome, layout.pointerType.isSome, layout.pointerDataType.isSome, layout.enumTagType.isSome].filter (fun enabled => enabled)
  if !constructors.isEmpty then
    unless constructors.size == 1 &&
        layout.primitiveRecipe.isNone && layout.sizeBytes.isNone &&
        layout.abiAlignBytes.isNone && layout.unadjustedAbiAlignBytes.isNone &&
        layout.fields.isNone && layout.variantsLayout.isNone &&
        layout.backendRepresentation.isNone do
      throw s!"{path}: structural recipe cannot contain eager layout results or another recipe"
    return ()
  if let some recipe := layout.primitiveRecipe then
    unless ["bool", "char", "i8", "i16", "i32", "i64", "i128", "isize",
        "u8", "u16", "u32", "u64", "u128", "usize", "f16", "f32", "f64", "f128",
        "fn_pointer", "never"].contains recipe do
      throw s!"{path}: unknown primitive layout recipe"
    unless layout.sizeBytes.isNone && layout.abiAlignBytes.isNone &&
        layout.unadjustedAbiAlignBytes.isNone && layout.fields.isNone &&
        layout.variantsLayout.isNone && layout.backendRepresentation.isNone do
      throw s!"{path}: primitive recipe cannot contain eager layout results"
    return ()
  match layout.backendRepresentation with
  | some repr => validateBackendRepr repr s!"{path}.backend_repr"
  | none => pure ()
  match layout.variantsLayout with
  | some variants =>
    match variants.tagEncoding with
    | some encoding => validateTagEncoding encoding s!"{path}.variants.tag_encoding"
    | none => if variants.kind == .multiple then throw (s!"{path}.variants.tag_encoding" ++ ": " ++ "multi-variant layout is missing tag encoding")
    match variants.tag with
    | some scalar => validateScalarLayout scalar s!"{path}.variants.tag"
    | none => pure ()
    for variant in variants.variants do
      validateBackendRepr variant.backendRepr s!"{path}.variants[{variant.variantIndex}].backend_repr"
  | none => pure ()

def validateBody (body : Body) (path : String) : Except String Unit := do
  validatePromotedBody body.promotedBodies (path ++ ".promoted_bodies")
  for (entry, index) in body.backtraceSpans.toList.zipIdx do
    unless entry.position.bytePosition < 2^32 do
      throw s!"{path}.backtrace_spans[{index}]: compiler BytePos exceeds u32"

end Miri.Input.LocalValidation
