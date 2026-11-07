import Miri.Input.AllocIdWorldValidation
import Miri.Input.Reader.PrimitiveTypes
import Miri.Input.Reader.TargetLayout
import Miri.Input.Reader.BodyValidation
import Miri.Input.Reader.ReferenceValidation
import Miri.Input.Reader.AllocationMemory
import Miri.Input.Reader.Types
import Miri.Input.Reader.Covariance
import Miri.Input.Reader.ProgramMIR
import Miri.Input.Model
import Miri.Input.Reader.Producer
import Miri.Input.Reader.BodySpans
import Miri.Input.Reader.RootSpan
import Miri.Input.Reader.Layout
import Miri.Input.Reader.Projections
import Miri.Input.Reader.Abi
import Miri.Input.Reader.AbiQueries
import Miri.Input.Reader.TypeRelations
import Miri.Input.Reader.CompilerFacts
import Miri.Input.Reader.Vtables
import Miri.Input.Reader.Predicates

namespace Miri.Input
open Lean DecoderValues
open Reader (inspectJson jsonField? jsonFieldAs?)
variable [Reader.JsonFields]

private def primitiveLayoutObligations (primitive : PrimitiveLayout) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match primitive.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .integer =>
    if primitive.integerKind.isNone || primitive.signed.isNone then
      issues := issues.push ⟨path, "integer primitive layout is missing integer kind or signedness"⟩
    match primitive.integerKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "integer_kind"))
    | _ => pure ()
  | .float =>
    if primitive.floatKind.isNone then issues := issues.push ⟨path, "float primitive layout is missing float kind"⟩
    match primitive.floatKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "float_kind"))
    | _ => pure ()
  | .pointer =>
    if primitive.addressSpace.isNone then issues := issues.push ⟨path, "pointer primitive layout is missing address space"⟩
  return issues

private def scalarLayoutObligations (scalar : ScalarLayout) (path : String) : Array Obligation := Id.run do
  let mut issues := primitiveLayoutObligations scalar.primitive (joinPath path "primitive")
  match scalar.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .initialized =>
    if scalar.validRange.isNone then issues := issues.push ⟨path, "initialized scalar layout is missing its valid range"⟩
  | .union => pure ()
  return issues

private def backendReprObligations (repr : BackendRepr) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? repr.status path).toArray
  match repr.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | _ => pure ()
  for (key, scalar) in [("scalar", repr.scalar), ("first", repr.first), ("second", repr.second), ("element", repr.element)] do
    match scalar with
    | some value => issues := issues ++ scalarLayoutObligations value (joinPath path key)
    | none => pure ()
  return issues

private def enumObligations (status : PayloadStatus) (tag : String) (known : List String)
    (path description : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? status path).toArray
  if !known.contains tag then
    issues := issues.push ⟨joinPath path "kind", s!"unrecognized {description} tag `{tag}`"⟩
  return issues

private def canonicalAbiObligations (abi : CanonicalAbi) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? abi.status path).toArray
  match abi.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .arm =>
    match abi.armCall with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "arm_call"))
    | none => issues := issues.push ⟨joinPath path "arm_call", "ARM calling convention is missing its call kind"⟩
    | _ => pure ()
  | .interrupt =>
    match abi.interruptKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "interrupt_kind"))
    | none => issues := issues.push ⟨joinPath path "interrupt_kind", "interrupt calling convention is missing its interrupt kind"⟩
    | _ => pure ()
  | .x86 =>
    match abi.x86Call with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "x86_call"))
    | none => issues := issues.push ⟨joinPath path "x86_call", "x86 calling convention is missing its call kind"⟩
    | _ => pure ()
  | _ => pure ()
  return issues

private def abiAttributesObligations (attrs : AbiAttributes) (path : String) : Array Obligation := Id.run do
  let mut issues := enumObligations attrs.argExtension.status attrs.argExtension.tag ["none", "zero_extend", "sign_extend"]
      (joinPath path "arg_extension") "argument extension"
  issues := issues ++ enumObligations attrs.captures.status attrs.captures.tag ["none", "address", "read_only", "unrestricted"]
      (joinPath path "captures") "capture mode"
  return issues

private def abiRegisterObligations (reg : AbiRegister) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match reg.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .vector =>
    match reg.hintElement with
    | none => issues := issues.push ⟨joinPath path "kind.hint_element", "vector ABI register is missing its element hint"⟩
    | some hint =>
      let hintPath := joinPath path "kind.hint_element"
      issues := issues ++ (statusObligation? hint.status hintPath).toArray
      if let .unsupported tag := hint.kind then
        issues := issues.push ⟨joinPath hintPath "kind", s!"unrecognized register element tag `{tag}`"⟩
  | _ => pure ()
  return issues

private def abiPassModeObligations (mode : AbiPassMode) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match mode.kind with
  | .unknown tag => issues := issues.push ⟨joinPath path "kind", s!"unrecognized ABI pass mode `{tag}`"⟩
  | _ => pure ()
  for (attrs, index) in mode.attributes.toList.zipIdx do
    issues := issues ++ abiAttributesObligations attrs s!"{path}.attributes[{index}]"
  match mode.castTarget with
  | some target =>
    for (register, index) in target.prefixRegisters.toList.zipIdx do
      issues := issues ++ abiRegisterObligations register s!"{path}.target.prefix_registers[{index}]"
    issues := issues ++ abiRegisterObligations target.restRegister (joinPath path "target.rest_register")
    issues := issues ++ abiAttributesObligations target.attributes (joinPath path "target.attributes")
  | none => pure ()
  match mode.indirectMode with
  | some tag => issues := issues ++ enumObligations tag.status tag.tag ["pointer", "on_stack", "amdgpu_kernel_argument"] (joinPath path "mode") "indirect mode"
  | none => pure ()
  return issues

private def allocationMemoryObligations (memory : AllocationMemory) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match memory.mutability with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "mutability"))
  | .mutable | .immutable => pure ()
  if memory.alignBytes == 0 then issues := issues.push ⟨joinPath path "align_bytes", "allocation alignment must be nonzero"⟩
  return issues

private def tagEncodingObligations (encoding : TagEncoding) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? encoding.status path).toArray
  match encoding.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .direct => pure ()
  | .niche =>
    if encoding.untaggedVariant.isNone || encoding.nicheVariants.isNone || encoding.nicheStart.isNone then
      issues := issues.push ⟨path, "niche tag encoding is missing its structured variant range or niche start"⟩
    match encoding.nicheVariants with
    | some (first, last) => if last < first then issues := issues.push ⟨joinPath path "niche_variants", "inclusive niche range has its end before its start"⟩
    | none => pure ()
  return issues

private def promotedBodyObligations (promoted : Array PromotedBody) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  for entry in promoted do
    if entry.body.isNone then
      issues := issues.push ⟨s!"{path}[{entry.index}]", "promoted MIR body is absent; cannot import it as typed MIR"⟩
    if entry.status != .supported then
      if let some issue := statusObligation? entry.status s!"{path}[{entry.index}].status" then
        issues := issues.push issue
  return issues

private def virtualIdentityObligations (raw : Json) (types : Array TypeNode)
    (instances : Array InstanceNode) : Array Obligation := Id.run do
  let mut issues := #[]
  for (node, index) in instances.toList.zipIdx do
    if node.kind != .virtualDispatchTarget || node.status != .supported then continue
    let base := s!"$.instances[{index}]"
    let payload := node.payload
    if ((jsonFieldAs? String payload) "body_status").toOption != some "not_applicable" then
      issues := issues.push ⟨base ++ ".body_status", "virtual dispatch identity must explicitly have no executable MIR body"⟩
    if node.body.isSome then
      issues := issues.push ⟨base ++ ".body", "virtual dispatch identity cannot carry a fabricated MIR body"⟩
    let kind := ((jsonField? payload) "instance_kind").toOption.getD .null
    if ((jsonFieldAs? String kind) "kind").toOption != some "virtual" then
      issues := issues.push ⟨base ++ ".instance_kind.kind", "virtual dispatch target must retain rustc InstanceKind::Virtual"⟩
    if ((jsonField? kind) "def_id").toOption != ((jsonField? payload) "def_id").toOption then
      issues := issues.push ⟨base ++ ".instance_kind.def_id", "virtual InstanceKind DefId disagrees with catalog DefId"⟩
    if ((jsonField? kind) "dispatch_slot").toOption != ((jsonField? payload) "dispatch_slot").toOption then
      issues := issues.push ⟨base ++ ".instance_kind.dispatch_slot", "virtual InstanceKind slot disagrees with catalog slot"⟩
    let identity := ((jsonField? payload) "virtual_identity").toOption.getD .null
    if ((jsonFieldAs? String identity) "status").toOption != some "supported" then
      issues := issues.push ⟨base ++ ".virtual_identity.status", "virtual method identity/signature query is unresolved"⟩
    let functionType := ((jsonField? identity) "function_type").toOption.getD .null
    let typeId := ((jsonFieldAs? Nat functionType) "type_id").toOption
    match typeId with
    | none => issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity is missing its compiler function type"⟩
    | some id =>
      let typeMatches := types.filter (·.id == id)
      if typeMatches.size != 1 then
        issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity references a missing or ambiguous type"⟩
      else if let some ty := typeMatches[0]? then
        if ty.shapeKind != .functionPointer && ty.shapeKind != .functionDefinition then
          issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity type is not a compiler function value"⟩
    let abi := ((jsonField? identity) "fn_abi").toOption.getD .null
    if ((jsonFieldAs? String abi) "status").toOption != some "supported" then
      issues := issues.push ⟨base ++ ".virtual_identity.fn_abi.status", "virtual method FnAbi query is unresolved"⟩
    let abiValue := ((jsonField? abi) "value").toOption
    let catalog := (((jsonField? raw) "compiler_instance_abis").bind Json.getArr?).toOption.getD #[]
    let abiRows := catalog.filter fun row =>
      ((jsonFieldAs? Nat row) "instance_id").toOption == some node.id &&
      ((jsonField? row) "instance_kind").toOption == ((jsonField? payload) "instance_kind").toOption &&
      ((jsonField? row) "generic_args").toOption == ((jsonField? payload) "generic_args").toOption
    if abiRows.size != 1 then
      issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "virtual identity must match one exact full-instance FnAbi query"⟩
    else if let some row := abiRows[0]? then
      let query := ((jsonField? row) "abi_query").toOption.getD .null
      if ((jsonFieldAs? String query) "status").toOption != some "supported" then
        issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "matching full-instance FnAbi query is unresolved"⟩
      else if abiValue != ((jsonField? query) "value").toOption then
        issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "virtual identity FnAbi disagrees with the exact full-instance FnAbi query"⟩
  return issues

private def extraSemanticObligations (raw : Json) (types : Array TypeNode) (layoutTable : Miri.MIR.SharedTable Layout) (allocations : Array AllocationNode)
    (instances : Array InstanceNode) (abis : AbiTables) (bodies : Array Body) : Array Obligation := Id.run do
  let mut issues := #[]
  issues := issues ++ virtualIdentityObligations raw types instances
  for node in types do
    let .ok layout := layoutTable.lookup node.layoutId
      | issues := issues.push ⟨s!"types[{node.id}].layout", "missing layout table entry"⟩; continue
    match node.shapeKind with
    | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].shape.kind")
    | _ => pure ()
    let shapePath := s!"types[{node.id}].shape"
    if node.shapeStatus == .supported then
      match node.shapeKind, node.shapeMetadata.signedKind, node.shapeMetadata.unsignedKind,
          node.shapeMetadata.floatKind, node.shapeMetadata.adtKind with
      | .int, none, _, _, _ => issues := issues.push ⟨joinPath shapePath "signed_kind", "signed integer type shape is missing its exact integer type"⟩
      | .int, some (.known kind), _, _, _ =>
        if !kind.signed then
          issues := issues.push ⟨joinPath shapePath "signed_kind", "signed integer type shape carries an unsigned integer kind"⟩
      | .uint, _, none, _, _ => issues := issues.push ⟨joinPath shapePath "unsigned_kind", "unsigned integer type shape is missing its exact integer type"⟩
      | .uint, _, some (.known kind), _, _ =>
        if kind.signed then
          issues := issues.push ⟨joinPath shapePath "unsigned_kind", "unsigned integer type shape carries a signed integer kind"⟩
      | .float, _, _, none, _ => issues := issues.push ⟨joinPath shapePath "float_kind", "float type shape is missing its exact float type"⟩
      | .adt, _, _, _, none => issues := issues.push ⟨joinPath shapePath "adt_kind", "ADT type shape is missing its struct/union/enum kind"⟩
      | _, _, _, _, _ => pure ()
    match node.shapeMetadata.signedKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "signed_kind"))
    | _ => pure ()
    match node.shapeMetadata.unsignedKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "unsigned_kind"))
    | _ => pure ()
    match node.shapeMetadata.floatKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "float_kind"))
    | _ => pure ()
    match node.shapeMetadata.adtKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "adt_kind"))
    | _ => pure ()
    match layout.kind with
    | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.kind")
    | .layoutQueryError => issues := issues.push ⟨s!"types[{node.id}].layout", "rustc could not provide a concrete type layout"⟩
    | .layout => pure ()
    match layout.fields with
    | some fields =>
      match fields.kind with
      | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.fields.kind")
      | _ => pure ()
    | none => pure ()
    match layout.backendRepresentation with
    | some repr => issues := issues ++ backendReprObligations repr s!"types[{node.id}].layout.backend_repr"
    | none => pure ()
    match layout.variantsLayout with
    | some variants =>
      issues := issues ++ (statusObligation? variants.status s!"types[{node.id}].layout.variants").toArray
      match variants.kind with
      | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.variants.kind")
      | _ => pure ()
      match variants.tagEncoding with
      | some encoding => issues := issues ++ tagEncodingObligations encoding s!"types[{node.id}].layout.variants.tag_encoding"
      | none => if variants.kind == .multiple then issues := issues.push ⟨s!"types[{node.id}].layout.variants.tag_encoding", "multi-variant layout is missing tag encoding"⟩
      match variants.tag with
      | some scalar => issues := issues ++ scalarLayoutObligations scalar s!"types[{node.id}].layout.variants.tag"
      | none => pure ()
      for variant in variants.variants do
        issues := issues ++ backendReprObligations variant.backendRepr s!"types[{node.id}].layout.variants[{variant.variantIndex}].backend_repr"
    | none => pure ()
  for node in allocations do
    let allocPath := s!"allocations[{node.id}]"
    match node.kind, node.data with
    | .unknown, _ => issues := issues.push ⟨s!"{allocPath}.kind", "allocation kind is missing"⟩
    | .other tag, _ => issues := issues.push ⟨s!"{allocPath}.kind", s!"unrecognized allocation kind `{tag}`"⟩
    | .memory, some (.memory memory) =>
      issues := issues ++ allocationMemoryObligations memory allocPath
    | .function, some (.function function) =>
      if function.definitionPath.isEmpty then issues := issues.push ⟨s!"{allocPath}.instance_def_path", "function allocation is missing its definition path"⟩
    | .static, some (.static static) =>
      if static.definitionPath.isEmpty then issues := issues.push ⟨s!"{allocPath}.def_path", "static allocation is missing its definition path"⟩
      match static.initializer, static.globalInfo with
      | some initializer, _ =>
        issues := issues ++ allocationMemoryObligations initializer (joinPath allocPath "initializer")
      | none, some info =>
        if !info.foreignItem then issues := issues.push ⟨joinPath allocPath "initializer", "non-foreign static is missing its initializer image"⟩
      | none, none =>
        issues := issues.push ⟨joinPath allocPath "initializer", "static without an initializer lacks exact foreign-item compiler evidence"⟩
    | .vtable, some (.vtable vtable) =>
      if let some issue := statusObligation? vtable.layoutStatus s!"{allocPath}.layout_status" then issues := issues.push issue
      for (predicate, index) in vtable.predicates.toList.zipIdx do
        let pPath := s!"{allocPath}.predicates[{index}]"
        if let some issue := statusObligation? predicate.status (joinPath pPath "status") then issues := issues.push issue
        match predicate.kind with
        | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath pPath "kind"))
        | _ => pure ()
      for (entry, index) in vtable.entries.toList.zipIdx do
        let ePath := s!"{allocPath}.entries[{index}]"
        if let some issue := statusObligation? entry.status (joinPath ePath "status") then issues := issues.push issue
        match entry.kind with
        | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath ePath "kind"))
        | _ => pure ()
    | .typeId, some (.typeId _) => pure ()
    | _, none => if node.status == .supported then issues := issues.push ⟨allocPath, "supported allocation is missing its typed payload"⟩
    | _, some _ => issues := issues.push ⟨allocPath, "allocation kind and typed payload disagree"⟩
  for node in instances do
    match node.kind with
    | .other tag => issues := issues.push ⟨s!"instances[{node.id}].kind", s!"unrecognized instance kind `{tag}`"⟩
    | .instanceMirTemplate => issues := issues.push ⟨s!"instances[{node.id}].kind", "generic MIR template is not a substituted executable instance body"⟩
    | .instanceMir =>
      if node.body.isNone then
        issues := issues.push ⟨s!"instances[{node.id}].body", "instance MIR is missing its decoded body"⟩
      match node.bodyInstantiation with
      | none => issues := issues.push ⟨s!"instances[{node.id}].body_instantiation", "instance body is missing substitution/normalization evidence"⟩
      | some detail =>
        if let some issue := statusObligation? detail.status s!"instances[{node.id}].body_instantiation.status" then issues := issues.push issue
        if detail.tag != "substituted_and_normalized" then
          issues := issues.push ⟨s!"instances[{node.id}].body_instantiation.kind", s!"unsupported instance body transformation `{detail.tag}`"⟩
      if node.bodyTemplateIsPolymorphic.isNone then
        issues := issues.push ⟨s!"instances[{node.id}].body_template_is_polymorphic", "instance lacks polymorphism metadata for its body template"⟩
      if node.instanceArgsAreMonomorphic != some true then
        issues := issues.push ⟨s!"instances[{node.id}].instance_args_are_monomorphic", "instance arguments are not known to be monomorphic"⟩
    | .intrinsicWithoutMir => issues := issues.push ⟨s!"instances[{node.id}]", "intrinsic instance has no imported MIR body"⟩
    | .intrinsicDispatch =>
      let base := s!"instances[{node.id}]"
      if node.status != .supported then
        issues := issues.push ⟨joinPath base "status", "intrinsic dispatch identity is not supported by the source compiler facts"⟩
      if node.body.isSome then
        issues := issues.push ⟨joinPath base "body", "intrinsic dispatch identity cannot carry fabricated MIR"⟩
      let instanceKind := ((jsonField? node.payload) "instance_kind").toOption.getD .null
      let tag := ((jsonFieldAs? String instanceKind) "kind").toOption
      if tag != some "intrinsic" && tag != some "llvm_intrinsic" then
        issues := issues.push ⟨joinPath base "instance_kind.kind", "intrinsic dispatch requires exact rustc Intrinsic or LlvmIntrinsic identity"⟩
      let topDefId := node.definitionId
      let nestedDefIdJson := ((jsonField? instanceKind) "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind fun value =>
        match (jsonFieldAs? Nat value) "crate", (jsonFieldAs? Nat value) "index" with
        | .ok crate, .ok index => some ⟨crate, index⟩
        | _, _ => none
      if topDefId.isNone then
        issues := issues.push ⟨joinPath base "def_id", "intrinsic dispatch requires an exact top-level rustc DefId"⟩
      if nestedDefId.isNone then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "intrinsic dispatch requires an exact nested rustc DefId"⟩
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "intrinsic identity DefId disagrees with its instance record"⟩
    | .foreignItemNoMir =>
      let base := s!"instances[{node.id}]"
      if node.status != .supported then
        issues := issues.push ⟨joinPath base "status", "foreign item dispatch identity is not supported by source compiler facts"⟩
      if node.body.isSome then
        issues := issues.push ⟨joinPath base "body", "foreign declaration cannot carry fabricated MIR"⟩
      if ((jsonFieldAs? Bool node.payload) "foreign_item").toOption != some true then
        issues := issues.push ⟨joinPath base "foreign_item", "no-MIR foreign dispatch requires exact rustc is_foreign_item=true evidence"⟩
      let symbol := ((jsonField? node.payload) "symbol_name").toOption.getD .null
      if ((jsonFieldAs? String symbol) "status").toOption != some "supported" ||
          (((jsonFieldAs? String symbol) "value").toOption.getD "").isEmpty then
        issues := issues.push ⟨joinPath base "symbol_name", "no-MIR foreign dispatch requires an exact nonempty rustc symbol name"⟩
      let instanceKind := ((jsonField? node.payload) "instance_kind").toOption.getD .null
      if ((jsonFieldAs? String instanceKind) "kind").toOption != some "item" then
        issues := issues.push ⟨joinPath base "instance_kind.kind", "foreign dispatch requires exact rustc Item identity"⟩
      let topDefId := node.definitionId
      let nestedDefIdJson := ((jsonField? instanceKind) "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind fun value =>
        match (jsonFieldAs? Nat value) "crate", (jsonFieldAs? Nat value) "index" with
        | .ok crate, .ok index => some ⟨crate, index⟩
        | _, _ => none
      if topDefId.isNone then
        issues := issues.push ⟨joinPath base "def_id", "foreign dispatch requires an exact top-level rustc DefId"⟩
      if nestedDefId.isNone then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "foreign dispatch requires an exact nested rustc DefId"⟩
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "foreign identity DefId disagrees with its instance record"⟩
    | .virtualDispatch => issues := issues.push ⟨s!"instances[{node.id}]", "virtual dispatch operation lacks a complete abstract instance identity"⟩
    | .virtualDispatchTarget => pure ()
    | .instanceMirUnavailable => issues := issues.push ⟨s!"instances[{node.id}]", "rustc did not provide an instance MIR body"⟩
    | .symbolIdentityOnly =>
      if node.body.isSome then
        issues := issues.push ⟨s!"instances[{node.id}].body", "symbol identity catalog row must not provide an executable MIR body"⟩
  for (entry, abiIndex) in abis.functions.toList.zipIdx do
    let some (.ok abi) := entry | continue
    issues := issues ++ canonicalAbiObligations abi.callingConvention s!"function_abis[{abiIndex}].calling_convention"
    match abis.argumentLists.lookup abi.arguments with
    | .error id => issues := issues.push ⟨s!"function_abis[{abiIndex}]", s!"invalid argument list {id}"⟩
    | .ok arguments =>
      for id in arguments.push abi.returnValue do
        match abis.arguments.lookup id with
        | .error id => issues := issues.push ⟨s!"function_abis[{abiIndex}]", s!"invalid argument {id}"⟩
        | .ok arg => issues := issues ++ abiPassModeObligations arg.mode s!"function_abis[{abiIndex}].arguments[{id}].mode"
  for (body, index) in bodies.toList.zipIdx do
    issues := issues ++ promotedBodyObligations body.promotedBodies s!"bodies[{index}].promoted_bodies"
  for node in instances do
    issues := issues ++ promotedBodyObligations node.promotedBodies s!"instances[{node.id}].promoted_bodies"
  return issues

private def selectedScopeObligations (scope : SelectedScope) (bodies : Array Body)
    (instances : Array InstanceNode) : Array Obligation := Id.run do
  let mut issues := #[]
  if scope.kind != "rooted_structural_closure" then
    issues := issues.push ⟨"$.selected_scope.kind", s!"unrecognized selected-scope kind `{scope.kind}`"⟩
  if scope.statusText != "complete" || scope.status != .supported then
    issues := issues.push ⟨"$.selected_scope.status", s!"selected scope is not complete (`{scope.statusText}`)"⟩
  if scope.semantics != "structural_export_closure_only" then
    issues := issues.push ⟨"$.selected_scope.semantics", s!"unrecognized scope guarantee `{scope.semantics}`"⟩
  if scope.roots.isEmpty then issues := issues.push ⟨"$.selected_scope.roots", "selected structural closure has no root"⟩
  for (root, index) in scope.roots.toList.zipIdx do
    let resolvedBody := bodies.any fun body =>
      body.definitionId == some root.definitionId && body.defPath == root.defPath
    let resolvedInstance := instances.any fun inst =>
      inst.definitionId == some root.definitionId && inst.defPath == some root.defPath
    if !resolvedBody && !resolvedInstance then
      issues := issues.push ⟨s!"$.selected_scope.roots[{index}]", "selected DefId and path do not resolve to an emitted body or instance"⟩
  if scope.unresolvedEvidence.isEmpty then
    for (message, index) in scope.unresolvedObligations.toList.zipIdx do
      issues := issues.push ⟨s!"$.selected_scope.unresolved_obligations[{index}]", message⟩
  else issues := issues ++ scope.unresolvedEvidence
  return issues

private def globalCompletenessPath (path : String) : Bool :=
  path == "$.completeness.status" || path.startsWith "$.completeness.unresolved_obligations["

/-- Query demand belongs to the interpreter entry that performs it. A selected
MIR structural closure does not perform startup exported-symbol traversal or
arbitrary foreign-shim catalog queries. Unknown families remain structural. -/
private inductive QueryDependencyRole where
  | structural | foreignShim | programStartup | callHelper | runtimeCast | intrinsicValue
  | nativeCallbackSignature | runtimeTypeQuery | namedPathStatic | runtimeVirtual
  | runtimeCallMetadata
  deriving BEq

/-- Only the checked status of an actual array-entry query is demand-local.
Unknown descendants and malformed paths remain structural obligations. -/
private def exactCatalogStatus (path catalog suffix : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, ending] => head == "$." ++ catalog && !index.isEmpty &&
        index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && ending == suffix
    | _ => false
  | _ => false

private def exactVirtualResolutionStatus (path : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, suffix] => head == "$.compiler_runtime_queries.virtual" &&
        !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && suffix == ".resolved.status"
    | _ => false
  | _ => false

private def exactRuntimeInstanceFactStatus (path : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, suffix] => head == "$.compiler_runtime_queries.instances" &&
        !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") &&
        [".symbol_name.status", ".item_name.status", ".intrinsic_metadata.status",
          ".codegen_symbol_name.status"].contains suffix
    | _ => false
  | _ => false

private def exactLibcTypeLayoutStatus (path : String) : Bool :=
  let prefixText := "$.compiler_libc_type_layouts.entries."
  let suffixText := ".status"
  if !path.startsWith prefixText || !path.endsWith suffixText then false else
    let name := ((path.drop prefixText.length).dropEnd suffixText.length).toString
    let known := #[
      "_umtx_time", "addrinfo", "clockid_t", "dirent", "dirent64", "epoll_event",
      "iovec", "linger", "mach_timebase_info", "mode_t", "nfds_t", "off_t",
      "os_unfair_lock_s", "passwd", "pollfd", "pthread_attr_t", "pthread_cond_t",
      "pthread_condattr_t", "pthread_key_t", "pthread_mutex_t", "pthread_mutexattr_t",
      "pthread_rwlock_t", "pthread_t", "sa_family_t", "sem_t", "size_t", "sockaddr",
      "sockaddr_in", "sockaddr_in6", "sockaddr_storage", "socklen_t", "stack_t", "statx",
      "time_t", "timespec", "timeval", "timezone", "tm", "utsname", "wchar_t"]
    known.contains name && path == prefixText ++ name ++ suffixText

/-- These are the finite source-path type queries emitted by
`shim_abi::named_types`. Only their status leaves are demand-local; the
catalog payload and any unrecognized key remain structural evidence. -/
private def exactCompilerNamedTypeStatus (path : String) : Bool :=
  let prefixText := "$.compiler_named_types."
  let suffixText := ".status"
  if !path.startsWith prefixText || !path.endsWith suffixText then false else
    let key := ((path.drop prefixText.length).dropEnd suffixText.length).toString
    let known := #[
      "c_ulong", "off_t", "off64_t", "pid_t", "uid_t", "nfds_t",
      "wchar_t", "pthread_t", "pthread_key_t",
      "libc_c_void", "libc_c_void_pointer", "libc_c_char", "libc_c_char_pointer",
      "libc_sockaddr", "libc_sockaddr_pointer", "libc_timespec", "libc_timespec_pointer",
      "libc_socklen_t", "libc_socklen_t_pointer", "libc_iovec", "libc_iovec_pointer",
      "u32_pointer", "i32_pointer"]
    known.contains key && path == prefixText ++ key ++ suffixText

private def exactDropGlueStatus (path : String) : Bool :=
  let prefixText := "$.compiler_runtime_queries.types["
  if !path.startsWith prefixText then false else
    let rest := (path.drop prefixText.length).toString
    match rest.splitOn "]" with
    | [index, suffix] => !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && suffix == ".drop_glue.status"
    | _ => false

private def exactInstanceCatalogPath (path : String) : Bool := Id.run do
  let path := if path.startsWith "$." then (path.drop 2).toString else path
  if !path.startsWith "instances[" then return false
  let rest := (path.drop 10).toString
  let pieces := rest.splitOn "]"
  let [index, suffix] := pieces | return false
  if index.isEmpty || !index.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (index != "0" && index.startsWith "0") then return false
  return suffix == "" || suffix == ".status"

/-- Type rows are a compilation-wide catalog, while a rooted export can use
only a small part of that catalog. These exact leaves are compiler queries
whose status is checked by the corresponding runtime adapter when requested.
The whitelist deliberately excludes shape data and unknown descendants.
Required layout status is elevated independently below; compiler facts remain
demand-local and are checked when their exact providers are requested.
-/
private def exactTypeQueryStatus (path : String) : Bool := Id.run do
  if !path.startsWith "$.types[" then return false
  let rest := (path.drop 8).toString
  let parts := rest.splitOn "]"
  let [index, suffix] := parts | return false
  if index.isEmpty || !index.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (index != "0" && index.startsWith "0") then return false
  if suffix == ".layout.status" then return true
  let exactQueries := #[
    ".compiler_facts.type_id_hash.status",
    ".compiler_facts.discriminants.status",
    ".compiler_facts.projection_queries.status",
    ".compiler_facts.simd_size_and_type.status",
    ".compiler_facts.boolean_queries.is_unsafe_cell.status",
    ".compiler_facts.boolean_queries.has_erasable_regions.status",
    ".compiler_facts.boolean_queries.is_c_void.status",
    ".compiler_facts.boolean_queries.is_simd.status",
    ".compiler_facts.boolean_queries.is_box.status",
    ".compiler_facts.boolean_queries.is_global_box.status",
    ".compiler_facts.boolean_queries.is_dynamic.status",
    ".compiler_facts.boolean_queries.is_too_generic.status",
    ".compiler_facts.boolean_queries.is_monomorphic.status",
    ".compiler_facts.boolean_queries.is_monomorphic_enough.status",
    ".compiler_facts.boolean_queries.is_like_maybe_dangling.status",
    ".compiler_facts.boolean_queries.is_freeze.status",
    ".compiler_facts.boolean_queries.is_unpin.status",
    ".compiler_facts.boolean_queries.is_unsafe_unpin.status",
    ".compiler_facts.boolean_queries.needs_drop.status",
    ".compiler_facts.boolean_queries.opsem_inhabited.status",
    ".compiler_facts.boolean_queries.is_sized.status",
    ".compiler_facts.type_queries.discriminant_type.status",
    ".compiler_facts.type_queries.normalized.status",
    ".compiler_facts.type_queries.builtin_deref_explicit.status",
    ".compiler_facts.type_queries.builtin_deref_implicit.status",
    ".compiler_facts.type_queries.boxed_type.status",
    ".compiler_facts.type_queries.unsafe_binder_erased.status",
    ".compiler_facts.type_queries.metadata_tail.status",
    ".compiler_facts.type_queries.pointer_metadata_type.status"]
  return suffix == ".shape.constructor_identity.status" || exactQueries.contains suffix

/-- Compute the type rows structurally demanded by the selected source graph.
This is independent of `selected_scope.unresolved_obligations`, so editing a
root type's layout status without editing the producer's diagnostic list cannot
make that required layout disappear. References in compiler_facts are excluded:
they are separate compiler queries and are checked by their exact providers.
-/
private partial def collectGraphReferencesInto (j : Json)
    (result : Array (String × Nat)) : Array (String × Nat) := Id.run do
  match inspectJson j with
  | .obj fields =>
    if ((jsonFieldAs? String j) "status").toOption == some "debug_payload" then return result
    let mut result := result
    for (key, value) in fields.toList do
      if key == "normalization_template" || key == "compiler_facts" || key == "constructor_identity" then
        continue
      if key == "type_id" || key == "instance_id" || key == "allocation_id" then
        if let .ok id := (inspectJson value).getNat? then result := result.push (key,id)
      result := collectGraphReferencesInto value result
    return result
  | .arr values =>
    let mut result := result
    for value in values do result := collectGraphReferencesInto value result
    return result
  | _ => return result

private def collectGraphReferences (j : Json) : Array (String × Nat) :=
  collectGraphReferencesInto j #[]

private def rawArray (j : Json) (key : String) : Array Json :=
  (((jsonField? j) key).bind Json.getArr?).toOption.getD #[]

private partial def collectThreadLocalRefsInto (j : Json) (path : String)
    (found : Array (String × Json)) : Array (String × Json) := Id.run do
  match inspectJson j with
  | .obj fields =>
    if ((jsonFieldAs? String j) "status").toOption == some "debug_payload" then return found
    let mut found := if ((jsonFieldAs? String j) "kind").toOption == some "ThreadLocalRef" then found.push ⟨path,j⟩ else found
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
  -- Hash only the exact source definition path string. Candidate rows are
  -- checked with Json equality below, so arbitrary malformed Json values do
  -- not rely on a Json hash/equality law.
  let mut bodiesByDefinitionPath : Std.HashMap (Option String) (Array (Json × Nat)) := {}
  let mut indexedBodyPosition := 0
  for body in bodyRows do
    let key := (((jsonField? body) "def_path").toOption.bind fun value => ((inspectJson value).getStr?).toOption)
    bodiesByDefinitionPath := bodiesByDefinitionPath.insert key
      ((bodiesByDefinitionPath[key]?.getD #[]).push (body, indexedBodyPosition))
    indexedBodyPosition := indexedBodyPosition + 1
  let mut instancesByDefinitionPath : Std.HashMap (Option String) (Array (Json × Nat)) := {}
  let mut instancesById : Std.HashMap Nat Json := {}
  for inst in instanceRows do
    let key := (((jsonField? inst) "def_path").toOption.bind fun value => ((inspectJson value).getStr?).toOption)
    if let .ok id := ((jsonField? inst) "instance_id").bind Json.getNat? then
      instancesByDefinitionPath := instancesByDefinitionPath.insert key
        ((instancesByDefinitionPath[key]?.getD #[]).push (inst, id))
      if !(instancesById[id]?.isSome) then instancesById := instancesById.insert id inst
  let mut typesById : Std.HashMap Nat Json := {}
  for row in typeRows do
    if let .ok id := ((jsonField? row) "type_id").bind Json.getNat? then
      if !(typesById[id]?.isSome) then typesById := typesById.insert id row
  let mut allocationsById : Std.HashMap Nat Json := {}
  for row in allocationRows do
    if let .ok id := ((jsonField? row) "allocation_id").bind Json.getNat? then
      if !(allocationsById[id]?.isSome) then allocationsById := allocationsById.insert id row
  let mut requiredTls := #[]
  let mut pendingInstances := #[]
  let mut pendingAllocations := #[]
  let mut pendingTypes := #[]
  let (selectedBodies, selectedInstances) := if includeAllBodies && (optionalField j "selected_scope").isNone then
      (bodyRows.toList.zipIdx.toArray, #[])
    else Id.run do
      let mut selected := #[]
      let mut rootInstances := #[]
      for root in roots do
        let rootPath := ((jsonField? root) "def_path").toOption
        let rootDef := ((jsonField? root) "def_id").toOption
        let rootPathText := rootPath.bind fun value => ((inspectJson value).getStr?).toOption
        let rootBodyRows := (bodiesByDefinitionPath[rootPathText]?.getD #[]).filter fun (body, _) =>
          ((jsonField? body) "def_path").toOption == rootPath &&
            ((jsonField? body) "def_id").toOption == rootDef
        -- The canonical root instance is an independent structural dependency,
        -- even when its MIR body is emitted and does not refer to itself.
        for (inst, id) in instancesByDefinitionPath[rootPathText]?.getD #[] do
          if ((jsonField? inst) "def_path").toOption == rootPath &&
              ((jsonField? inst) "def_id").toOption == rootDef then
            rootInstances := rootInstances.push id
        selected := selected ++ rootBodyRows
      (selected, rootInstances)
  pendingInstances := pendingInstances ++ selectedInstances
  for (body,bodyIndex) in selectedBodies do
      for reference in collectThreadLocalRefs body s!"$.bodies[{bodyIndex}]" do
        requiredTls := requiredTls.push reference
      for (kind,id) in collectGraphReferences body do
        if kind == "type_id" then pendingTypes := pendingTypes.push id
        else if kind == "instance_id" then pendingInstances := pendingInstances.push id
        else if kind == "allocation_id" then pendingAllocations := pendingAllocations.push id
  let mut visitedTypes := #[]
  let mut visitedTypeIds : Std.HashMap Nat Unit := {}
  let mut visitedInstances := #[]
  let mut visitedInstanceIds : Std.HashMap Nat Unit := {}
  let mut visitedAllocations := #[]
  let mut visitedAllocationIds : Std.HashMap Nat Unit := {}
  while !pendingTypes.isEmpty || !pendingInstances.isEmpty || !pendingAllocations.isEmpty do
    let typeRefs := pendingTypes
    pendingTypes := #[]
    for id in typeRefs do
      if visitedTypeIds[id]?.isSome then continue
      visitedTypes := visitedTypes.push id
      visitedTypeIds := visitedTypeIds.insert id ()
      if let some row := typesById[id]? then
        -- Only the compiler's source type shape participates here. Layout
        -- evidence itself is demanded separately; compiler_facts is a query catalog.
        if let .ok shape := (jsonField? row) "shape" then
          for (kind, child) in collectGraphReferences shape do
            if kind == "type_id" then pendingTypes := pendingTypes.push child
            else if kind == "instance_id" then pendingInstances := pendingInstances.push child
            else if kind == "allocation_id" then pendingAllocations := pendingAllocations.push child
    let instanceRefs := pendingInstances
    pendingInstances := #[]
    for id in instanceRefs do
      if visitedInstanceIds[id]?.isSome then continue
      visitedInstances := visitedInstances.push id
      visitedInstanceIds := visitedInstanceIds.insert id ()
      if let some row := instancesById[id]? then
        for reference in collectThreadLocalRefs row s!"$.instances[{id}]" do
          requiredTls := requiredTls.push reference
        for (key,child) in collectGraphReferences row do
          if key == "type_id" then pendingTypes := pendingTypes.push child
          if key == "instance_id" then pendingInstances := pendingInstances.push child
          if key == "allocation_id" then pendingAllocations := pendingAllocations.push child
    let allocationRefs := pendingAllocations
    pendingAllocations := #[]
    for id in allocationRefs do
      if visitedAllocationIds[id]?.isSome then continue
      visitedAllocations := visitedAllocations.push id
      visitedAllocationIds := visitedAllocationIds.insert id ()
      if let some row := allocationsById[id]? then
        for (key,child) in collectGraphReferences row do
          if key == "type_id" then pendingTypes := pendingTypes.push child
          if key == "instance_id" then pendingInstances := pendingInstances.push child
          if key == "allocation_id" then pendingAllocations := pendingAllocations.push child
  return ⟨visitedTypes, visitedInstances, visitedAllocations, requiredTls⟩

/-- The prepared allocator-world parser validates every field in its raw
subtree. Its opaque graph rows remain visible in the decoded tree, but only
rows reached from executable bodies are structural readiness blockers. -/
private def preparedWorldReadinessObligations (obligations : Array Obligation)
    (world : Option CompilerAllocIdWorld) (allocations : Array AllocationNode)
    (requiredAllocationIds : Array Nat) : Array Obligation := Id.run do
  let some world := world | return obligations
  let mut requiredIds : Std.HashMap Nat Unit := {}
  for allocationId in requiredAllocationIds do
    requiredIds := requiredIds.insert allocationId ()
  let mut undemandedOpaqueIds : Std.HashMap Nat Unit := {}
  for row in world.rawPool do
    if row.status == .opaque then
      if let some allocationId := row.opaqueAllocationId then
        if !requiredIds.contains allocationId then
          undemandedOpaqueIds := undemandedOpaqueIds.insert allocationId ()
  let mut undemandedOpaqueIndexes : Std.HashMap Nat Unit := {}
  for (node, index) in allocations.toList.zipIdx do
    if undemandedOpaqueIds.contains node.id then
      undemandedOpaqueIndexes := undemandedOpaqueIndexes.insert index ()
  obligations.filter fun issue => Id.run do
    if issue.path.startsWith "$.compiler_alloc_id_world." then return false
    let arrayPrefix := "$.allocations["
    if issue.path.startsWith arrayPrefix then
      let rest := (issue.path.drop arrayPrefix.length).toString
      let indexText := (rest.takeWhile (· != ']')).toString
      if rest.startsWith (indexText ++ "]") then
        if let .ok index := decimalNat indexText issue.path then
          if undemandedOpaqueIndexes.contains index then return false
    let semanticPrefix := "allocations["
    if issue.path.startsWith semanticPrefix then
      let rest := (issue.path.drop semanticPrefix.length).toString
      let allocationText := (rest.takeWhile (· != ']')).toString
      if rest.startsWith (allocationText ++ "]") then
        if let .ok allocationId := decimalNat allocationText issue.path then
          if undemandedOpaqueIds.contains allocationId then return false
    return true

/-- Symbol-only entries close compiler identity references but carry no MIR.
Their absence of a body is harmless while they are unused catalog rows, but
any row reached from a selected root or executable graph is an unresolved
structural dependency. -/
private def requiredIdentityOnlyInstanceObligations (instances : Array InstanceNode)
    (requiredIds : Array Nat) : Array Obligation := Id.run do
  let mut issues := #[]
  for (node, index) in instances.toList.zipIdx do
    if requiredIds.contains node.id && node.kind == .symbolIdentityOnly then
      issues := issues.push ⟨s!"$.instances[{index}].kind",
        "selected execution depends on a symbol identity that has no imported MIR body"⟩
  return issues

private def threadLocalShapeObligations (references : Array (String × Json)) : Array Obligation := Id.run do
  let mut issues := #[]
  for (path, value) in references do
    unless ((jsonFieldAs? String value) "status").toOption == some "supported" do continue
    let definition := ((jsonField? value) "def_id").toOption
    match definition with
    | none => issues := issues.push ⟨joinPath path "def_id", "supported ThreadLocalRef is missing its exact compiler DefId"⟩
    | some defId =>
      for key in ["crate", "index"] do
        if (((jsonField? defId) key).bind Json.getNat?).toOption.isNone then
          issues := issues.push ⟨joinPath (joinPath path "def_id") key, "ThreadLocalRef DefId component must be an unsigned integer"⟩
    let info := ((jsonField? value) "global_info").toOption
    let mut foreign := false
    match info with
    | none => issues := issues.push ⟨joinPath path "global_info", "supported ThreadLocalRef is missing static compiler query evidence"⟩
    | some info =>
      if ((jsonFieldAs? String info) "status").toOption != some "supported" then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "status", "ThreadLocalRef static compiler query is unresolved"⟩
      if ((jsonFieldAs? Bool info) "is_static").toOption != some true then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "is_static", "ThreadLocalRef DefId is not confirmed as a static"⟩
      if ((jsonFieldAs? Bool info) "thread_local").toOption != some true then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "thread_local", "ThreadLocalRef DefId is not confirmed as thread-local"⟩
      foreign := ((jsonFieldAs? Bool info) "is_foreign_item").toOption.getD false
      if ((jsonFieldAs? Bool info) "is_foreign_item").toOption.isNone then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "is_foreign_item", "ThreadLocalRef static query lacks its foreign-item predicate"⟩
    let initializer := ((jsonField? value) "initializer").toOption
    match initializer with
    | none => issues := issues.push ⟨joinPath path "initializer", "supported ThreadLocalRef is missing exact initializer query evidence"⟩
    | some initializer =>
      let initializerPath := joinPath path "initializer"
      if ((jsonFieldAs? String initializer) "status").toOption == some "supported" then
        let allocation := ((jsonField? initializer) "allocation").toOption
        match allocation with
        | none => issues := issues.push ⟨joinPath initializerPath "allocation", "supported TLS initializer is missing its allocation image"⟩
        | some allocation =>
          let allocationPath := joinPath initializerPath "allocation"
          match parseAllocationMemory allocation allocationPath with
          | .error reason => issues := issues.push ⟨allocationPath, reason⟩
          | .ok memory =>
            if let some info := info then
              match ((jsonField? info) "size_bytes").bind Json.getNat? with
              | .ok size => if size != memory.sizeBytes then
                  issues := issues.push ⟨joinPath allocationPath "size_bytes", "TLS initializer size disagrees with static compiler query"⟩
              | .error _ => issues := issues.push ⟨joinPath (joinPath path "global_info") "size_bytes", "TLS static query is missing its allocation size"⟩
              match ((jsonField? info) "align_bytes").bind Json.getNat? with
              | .ok align => if align != memory.alignBytes then
                  issues := issues.push ⟨joinPath allocationPath "align_bytes", "TLS initializer alignment disagrees with static compiler query"⟩
              | .error _ => issues := issues.push ⟨joinPath (joinPath path "global_info") "align_bytes", "TLS static query is missing its allocation alignment"⟩
      else if foreign && ((jsonFieldAs? String initializer) "status").toOption != some "unsupported" then
        issues := issues.push ⟨joinPath initializerPath "status", "foreign TLS initializer must remain an explicit unsupported query"⟩
  return issues

private def queryDependencyRole (path : String) : QueryDependencyRole :=
  if exactTypeQueryStatus path || exactDropGlueStatus path || exactInstanceCatalogPath path then .runtimeTypeQuery
  else if exactLibcTypeLayoutStatus path then .runtimeTypeQuery
  else if exactCompilerNamedTypeStatus path then .runtimeTypeQuery
  else if exactCatalogStatus path "compiler_named_constants" ".query.status" ||
      exactCatalogStatus path "compiler_named_constants" ".query.evaluation.status" ||
      exactCatalogStatus path "compiler_named_shim_abis" ".recipe.query.status" ||
      exactCatalogStatus path "compiler_named_shim_abis" ".recipe.query.abi_query.status" ||
      path == "$.compiler_runtime_queries.foreign_symbols.extern_statics.status" ||
      path == "$.compiler_runtime_queries.foreign_symbols.exported_candidates.status" then
    .foreignShim
  else if exactCatalogStatus path "compiler_named_statics" ".query.status" then .namedPathStatic
  else if exactCatalogStatus path "compiler_function_facts.helper_signatures" ".abi_query.status" then .callHelper
  -- Function type normalization and FnPtr ABI queries are catalogued for all
  -- exported types, then demanded only by the exact MIR call operation. The
  -- provider retains each failed query and reports it from the call hook.
  else if exactCatalogStatus path "compiler_function_facts.types" ".signature_query.status" ||
      exactCatalogStatus path "compiler_function_facts.pointer_abis" ".abi_query.status" then
    .runtimeCallMetadata
  -- Extern-static declaration and selected-export queries are materialized
  -- from the allocation graph, but their errors belong to exact symbol or
  -- DefId lookup at runtime, not to unrelated MIR paths. `compiler_fact`
  -- wraps the extern-static table in a `value` field; keep that envelope in
  -- each exact indexed path.
  else if exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.declarations" ".status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".declaration.status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".allocation.status" then
    .foreignShim
  else if exactCatalogStatus path "compiler_cast_queries" ".status" then .runtimeCast
  -- These exact compiler call-fact queries are checked by their source-owned
  -- providers when an operation requests them; an unavailable optional row
  -- does not make an unrelated selected MIR body malformed.
  else if exactRuntimeInstanceFactStatus path then .runtimeCallMetadata
  -- Candidate virtual resolutions are a cross-product over compiler vtable
  -- pairs. A failed nonselected row is retained as source evidence; the exact
  -- receiver/type/args lookup rejects it if execution actually demands it.
  else if exactVirtualResolutionStatus path then .runtimeVirtual
  else if exactCatalogStatus path "compiler_type_name_constants" ".status" ||
      exactCatalogStatus path "compiler_caller_location_constants" ".status" then .intrinsicValue
  -- alloc_addresses/mod.rs:167–174 demands this only when constructing a
  -- native compiler-function closure; its provider checks signature_query.status.
  else if exactCatalogStatus path "compiler_native_signature_queries" ".signature_query.status" then
    .nativeCallbackSignature
  else if path == "$.compiler_main_queries.link_sections.status" then .programStartup
  else .structural

private def obligationQueryRole (path : String) : QueryDependencyRole :=
  let canonical := if path.startsWith "$." then path else "$." ++ path
  let direct := queryDependencyRole canonical
  if direct != .structural then direct
  else queryDependencyRole (canonical ++ ".status")

private def pathCanReach (wanted path : String) : Bool :=
  wanted == path || wanted.startsWith (path ++ ".") || wanted.startsWith (path ++ "[")

private def jsonAtPathSegment (j : Json) (segment : String) : Option Json := Id.run do
  match segment.splitOn "[" with
  | [key] => return ((jsonField? j) key).toOption
  | [key, suffix] =>
    let pieces := suffix.splitOn "]"
    let [indexText, ""] := pieces | return none
    let .ok index := decimalNat indexText segment | return none
    let some arrayJson := ((jsonField? j) key).toOption | return none
    let some values := (inspectJson arrayJson).getArr?.toOption | return none
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
  ((jsonField? j) "type_id").toOption.bind (fun value => (inspectJson value).getNat?.toOption)

private def dynamicPredicateArray? (j : Json) (typeId : Nat) : Option (Array Json) := Id.run do
  let some types := ((((jsonField? j) "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    (((jsonFieldAs? Nat ty) "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := ((jsonField? ty) "shape").toOption | return none
  unless (((jsonFieldAs? String shape) "kind").toOption == some "dynamic_trait_object") do return none
  return (((jsonField? shape) "predicates").bind Json.getArr?).toOption

private def compilerBuiltinDerefType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := ((((jsonField? j) "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    (((jsonFieldAs? Nat ty) "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some facts := ((jsonField? ty) "compiler_facts").toOption | return none
  let some queries := ((jsonField? facts) "type_queries").toOption | return none
  let some query := ((jsonField? queries) "builtin_deref_explicit").toOption | return none
  unless (((jsonFieldAs? String query) "status").toOption == some "supported") do return none
  let some value := ((jsonField? query) "value").toOption | return none
  return jsonTypeId? value

private def exactLockstepTails? (j : Json) (source target : Nat) : Option Json := Id.run do
  let some rows := ((((jsonField? j) "compiler_cast_queries").bind Json.getArr?).toOption) | return none
  let matching := rows.filter fun row =>
    (((jsonFieldAs? String row) "query_kind").toOption == some "lockstep_tails") &&
    (((jsonFieldAs? String row) "typing_env").toOption == some "fully_monomorphized") &&
    (((jsonFieldAs? String row) "status").toOption == some "supported") &&
    (((jsonField? row) "input_source").toOption.bind jsonTypeId? == some source) &&
    (((jsonField? row) "input_target").toOption.bind jsonTypeId? == some target)
  unless matching.size == 1 do return none
  return matching[0]?

private def castOperandTypeId? (node : Json) : Option Nat := Id.run do
  let some operand := ((jsonField? node) "operand").toOption | return none
  let some operandKind := (((jsonField? operand) "kind").bind Json.getStr?).toOption | return none
  if operandKind == "Copy" || operandKind == "Move" then
    let some place := ((jsonField? operand) "place").toOption | return none
    let some ty := ((jsonField? place) "type").toOption | return none
    return jsonTypeId? ty
  else if operandKind == "Constant" then
    let some constant := ((jsonField? operand) "constant").toOption | return none
    let some ty := ((jsonField? constant) "type").toOption | return none
    return jsonTypeId? ty
  else return none

/-- The exporter may retain its salt-zero CTFE vtable probe as diagnostic
evidence, but it is not a runtime allocation identity. Only the exact probe
leaf attached to a supported concrete Unsize Cast and backed by a supported
exact-pair query is demand-local. The enclosing Cast must itself be supported;
all other statuses and descendants remain structural blockers. -/
def exactVtableProbeDiagnostic (j : Json) (path : String) : Bool := Id.run do
  let suffix := ".vtable_probe.status"
  unless path.endsWith suffix do return false
  let castPath := (path.dropEnd suffix.length).toString
  let some node := jsonAtPath j castPath | return false
  unless (((jsonFieldAs? String node) "status").toOption == some "supported") do return false
  unless (((jsonFieldAs? String node) "kind").toOption == some "Cast") do return false
  let some castKind := ((jsonField? node) "cast_kind").toOption | return false
  unless (((jsonFieldAs? String castKind) "status").toOption == some "supported") &&
      (((jsonFieldAs? String castKind) "kind").toOption == some "PointerCoercion") do return false
  let some coercion := ((jsonField? castKind) "coercion").toOption | return false
  unless (((jsonFieldAs? String coercion) "kind").toOption == some "Unsize") do return false
  let some sourceType := ((jsonField? node) "target_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  unless castOperandTypeId? node |>.isSome do return false
  let some operandTypeId := castOperandTypeId? node | return false
  let some queryRef := ((jsonField? node) "vtable_query").toOption | return false
  unless (((jsonFieldAs? String queryRef) "status").toOption == some "supported") do return false
  let some queryId := (((jsonField? queryRef) "query_id").bind Json.getNat?).toOption | return false
  let some querySource := ((jsonField? queryRef) "source_type").toOption | return false
  let some queryTarget := ((jsonField? queryRef) "target_type").toOption | return false
  unless jsonTypeId? querySource == some operandTypeId && jsonTypeId? queryTarget == some sourceTypeId do return false
  let some sourcePointee := ((jsonField? queryRef) "source_pointee_type").toOption | return false
  let some targetPointee := ((jsonField? queryRef) "target_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless compilerBuiltinDerefType? j operandTypeId == some sourcePointeeId &&
      compilerBuiltinDerefType? j sourceTypeId == some targetPointeeId do return false
  let some fullLockstep := exactLockstepTails? j operandTypeId sourceTypeId | return false
  let some fullLockstepValue := ((jsonField? fullLockstep) "value").toOption | return false
  unless (((jsonField? fullLockstepValue) "source_tail").toOption.bind jsonTypeId? == some operandTypeId) &&
      (((jsonField? fullLockstepValue) "target_tail").toOption.bind jsonTypeId? == some sourceTypeId) do return false
  let some sourceTail := ((jsonField? queryRef) "source_tail_type").toOption | return false
  let some targetTail := ((jsonField? queryRef) "target_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  let some inputType := ((jsonField? queryRef) "input_type").toOption | return false
  let some inputTypeId := jsonTypeId? inputType | return false
  unless inputTypeId == sourceTailId do return false
  let some queryPredicates := (((jsonField? queryRef) "input_predicates").bind Json.getArr?).toOption | return false
  let some targetPredicates := dynamicPredicateArray? j targetTailId | return false
  unless targetPredicates == queryPredicates do return false
  let some lockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some lockstepValue := ((jsonField? lockstep) "value").toOption | return false
  unless (((jsonField? lockstepValue) "source_tail").toOption.bind jsonTypeId? == some sourceTailId) &&
      (((jsonField? lockstepValue) "target_tail").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := ((((jsonField? j) "compiler_vtable_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    (((jsonFieldAs? Nat row) "query_id").toOption == some queryId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless (((jsonFieldAs? String row) "status").toOption == some "supported") do return false
  unless (((jsonField? row) "input_type").toOption.bind jsonTypeId? == some inputTypeId) do return false
  unless jsonTypeId? (((jsonField? row) "output_type").toOption.getD .null) |>.isSome do return false
  let some rowInputPredicates := (((jsonField? row) "input_predicates").bind Json.getArr?).toOption | return false
  unless rowInputPredicates == queryPredicates do return false
  unless (((jsonField? row) "output_predicates").bind Json.getArr?).isOk do return false
  unless (((jsonFieldAs? Bool row) "output_type_monomorphic_enough").toOption == some true) &&
      (((jsonFieldAs? Bool row) "output_predicates_monomorphic_enough").toOption == some true) do return false
  let some probe := ((jsonField? node) "vtable_probe").toOption | return false
  unless (((jsonFieldAs? String probe) "status").toOption == some "incomplete") &&
      (((jsonFieldAs? String probe) "kind").toOption == some "symbolic_vtable_allocation") &&
      ((((jsonFieldAs? String probe) "salt_policy").toOption.getD "").startsWith
        "exporter uses CTFE_ALLOC_SALT; Miri runtime allocation salts may be randomized") do return false
  unless ((jsonField? node) "vtable_allocation").toOption == some .null do return false
  unless (match (jsonField? probe) "allocation" with | .error _ => true | .ok _ => false) &&
      (match (jsonField? probe) "allocation_id" with | .error _ => true | .ok _ => false) do return false
  return true

/-- A dynamic-to-dynamic Unsize is represented by the runtime source-vtable
operation. Bind its descriptor to the Cast's complete types, both exact
lockstep queries, and the compiler's fully-monomorphized supertrait-slot row.
This validates evidence identity only; the runtime still obtains the table
from the actual source operand. -/
private def castUnsizingPointeeType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := ((((jsonField? j) "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty => ((jsonFieldAs? Nat ty) "type_id").toOption == some typeId
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := ((jsonField? ty) "shape").toOption | return none
  let some kind := ((jsonFieldAs? String shape) "kind").toOption | return none
  if kind == "reference" || kind == "raw_pointer" then
    return ((jsonField? shape) "pointee").toOption.bind jsonTypeId?
  else
    return some typeId

private def exactDynamicVtableUpcast? (j node descriptor : Json) : Bool := Id.run do
  unless (((jsonFieldAs? String node) "status").toOption == some "supported") &&
      (((jsonFieldAs? String node) "kind").toOption == some "Cast") do return false
  let some castKind := ((jsonField? node) "cast_kind").toOption | return false
  unless (((jsonFieldAs? String castKind) "status").toOption == some "supported") &&
      (((jsonFieldAs? String castKind) "kind").toOption == some "PointerCoercion") do return false
  let some coercion := ((jsonField? castKind) "coercion").toOption | return false
  unless ((jsonFieldAs? String coercion) "kind").toOption == some "Unsize" do return false
  unless (((jsonFieldAs? String descriptor) "status").toOption == some "supported") &&
      (((jsonFieldAs? String descriptor) "kind").toOption == some "dynamic_vtable_upcast") do return false
  let some sourceType := ((jsonField? descriptor) "source_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  let some targetType := ((jsonField? descriptor) "target_type").toOption | return false
  let some targetTypeId := jsonTypeId? targetType | return false
  unless castOperandTypeId? node == some sourceTypeId do return false
  unless (((jsonField? node) "target_type").toOption.bind jsonTypeId?) == some targetTypeId do return false

  let some sourcePointee := ((jsonField? descriptor) "source_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointee := ((jsonField? descriptor) "target_pointee_type").toOption | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless castUnsizingPointeeType? j sourceTypeId == some sourcePointeeId &&
      castUnsizingPointeeType? j targetTypeId == some targetPointeeId do return false

  let some fullLockstep := exactLockstepTails? j sourceTypeId targetTypeId | return false
  let some fullValue := ((jsonField? fullLockstep) "value").toOption | return false
  let some fullSourceTail := (((jsonField? fullValue) "source_tail").toOption.bind jsonTypeId?) | return false
  let some fullTargetTail := (((jsonField? fullValue) "target_tail").toOption.bind jsonTypeId?) | return false
  unless fullSourceTail == sourceTypeId && fullTargetTail == targetTypeId do return false

  let some sourcePointeeLockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some pointeeValue := ((jsonField? sourcePointeeLockstep) "value").toOption | return false
  let some sourceTail := ((jsonField? descriptor) "source_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTail := ((jsonField? descriptor) "target_tail_type").toOption | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  unless (((jsonField? pointeeValue) "source_tail").toOption.bind jsonTypeId?) == some sourceTailId &&
      (((jsonField? pointeeValue) "target_tail").toOption.bind jsonTypeId?) == some targetTailId do return false
  unless (dynamicPredicateArray? j sourceTailId).isSome &&
      (dynamicPredicateArray? j targetTailId).isSome do return false

  unless ((jsonFieldAs? String descriptor) "runtime_vtable").toOption ==
      some "source_operand_metadata" do return false
  let some embeddedQuery := ((jsonField? descriptor) "supertrait_slot_query").toOption | return false
  unless (((jsonFieldAs? String embeddedQuery) "status").toOption == some "supported") &&
      (((jsonFieldAs? String embeddedQuery) "query_kind").toOption == some "supertrait_slot") &&
      (((jsonFieldAs? String embeddedQuery) "typing_env").toOption == some "fully_monomorphized") &&
      (((jsonField? embeddedQuery) "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
      (((jsonField? embeddedQuery) "input_target").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := ((((jsonField? j) "compiler_cast_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    (((jsonFieldAs? String row) "query_kind").toOption == some "supertrait_slot") &&
    (((jsonFieldAs? String row) "typing_env").toOption == some "fully_monomorphized") &&
    (((jsonFieldAs? String row) "status").toOption == some "supported") &&
    (((jsonField? row) "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
    (((jsonField? row) "input_target").toOption.bind jsonTypeId? == some targetTailId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless (match (jsonField? row) "value" with
    | .ok .null => true
    | .ok value => ((inspectJson value).getNat?).isOk
    | .error _ => false) do return false
  return true

private partial def malformedDynamicVtableUpcastAux (root : Json) (node : JsonTraversalCache.Node) (path : String)
    (visited : Std.HashSet JsonTraversalCache.IdentityKey) : Option String × Std.HashSet JsonTraversalCache.IdentityKey := Id.run do
  let current := node.value
  let memoKey := node.identity
  match current with
  | .obj _ | .arr _ => pure ()
  | _ => return (none, visited)
  if node.shouldMemo && visited.contains memoKey then return (none, visited)
  let mut visited := if node.shouldMemo then visited.insert memoKey else visited
  match current with
  | .obj fields =>
    if ((jsonFieldAs? String current) "kind").toOption == some "Cast" then
      if let some descriptor := ((jsonField? current) "vtable_allocation").toOption then
        if ((jsonFieldAs? String descriptor) "kind").toOption == some "dynamic_vtable_upcast" &&
            ((jsonFieldAs? String descriptor) "status").toOption == some "supported" &&
            !exactDynamicVtableUpcast? root current descriptor then
          return (some (joinPath path "vtable_allocation"), visited)
    for ((key, value), childIndex) in fields.toList.zipIdx do
      let (badPath?, nextVisited) := malformedDynamicVtableUpcastAux root (node.child childIndex value) (joinPath path key) visited
      visited := nextVisited
      if let some badPath := badPath? then return (some badPath, visited)
  | .arr values =>
    for (value, childIndex) in values.toList.zipIdx do
      let (badPath?, nextVisited) := malformedDynamicVtableUpcastAux root (node.child childIndex value) s!"{path}[{childIndex}]" visited
      visited := nextVisited
      if let some badPath := badPath? then return (some badPath, visited)
  | _ => pure ()
  return (none, visited)

private def malformedDynamicVtableUpcast? (node : JsonTraversalCache.Node) : Option String :=
  (malformedDynamicVtableUpcastAux node.value node "$" {}).1

private partial def hasFailedStatusAt (j : Json) (wanted path : String) : Bool := Id.run do
  match inspectJson j with
  | .obj fields =>
    if ((jsonFieldAs? String j) "status").toOption == some "debug_payload" then return false
    if path == wanted then
      if let some status := ((jsonFieldAs? String j) "status").toOption then
        if status != "supported" then return true
    for (key, value) in fields.toList do
      let child := joinPath path key
      if pathCanReach wanted child && hasFailedStatusAt value wanted child then return true
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      let child := s!"{path}[{index}]"
      if pathCanReach wanted child && hasFailedStatusAt value wanted child then return true
  | _ => pure ()
  return false

/-- Copied catalog diagnostics inherit only their exact original query role.
The original obligations remain present; runtime providers still reject failed
queries when the corresponding source operation requests them. -/
private def retainedQueryDiagnosticRole (j : Json) (path : String) : QueryDependencyRole := Id.run do
  let pathPrefix := "$.selected_scope.retained_catalog_obligations["
  let suffix := "].status"
  unless path.startsWith pathPrefix && path.endsWith suffix do return .structural
  let indexText := ((path.drop pathPrefix.length).dropEnd suffix.length).toString
  let .ok index := decimalNat indexText path | return .structural
  unless toString index == indexText do return .structural
  let some records := ((((jsonField? j) "selected_scope").bind fun scope =>
      ((jsonField? scope) "retained_catalog_obligations").bind Json.getArr?).toOption)
    | return .structural
  let some record := records[index]? | return .structural
  let some sourcePath := (((jsonField? record) "path").bind Json.getStr?).toOption
    | return .structural
  unless hasFailedStatusAt j ("$." ++ sourcePath) "$" do return .structural
  if exactVtableProbeDiagnostic j ("$." ++ sourcePath ++ ".status") then return .runtimeCast
  return queryDependencyRole ("$." ++ sourcePath ++ ".status")

/-- Return exactly the selected-scope obligations that the readiness gate
blocks on. Keep diagnostics and the execution decision on this single
predicate so reports cannot drift from the fail-closed gate. -/
private def selectedScopeBlockingObligations (j : Json)
    (retainedRole : String → QueryDependencyRole) (obligations : Array Obligation)
    (requiredLayoutPaths : List String) (requiredInstancePaths : Array String) : Array Obligation :=
  obligations.filter fun issue =>
    (!globalCompletenessPath issue.path && !exactVtableProbeDiagnostic j issue.path &&
      obligationQueryRole issue.path == .structural &&
      retainedRole issue.path == .structural
      || issue.path == "$.selected_scope.kind" || issue.path == "$.selected_scope.status" ||
      issue.path == "$.selected_scope.semantics" || issue.path.startsWith "$.selected_scope.roots[" ||
      requiredLayoutPaths.contains issue.path ||
      requiredInstancePaths.contains issue.path)

private inductive ParsedDocument where
  | full (result : DecodeResult)
  | runtime (result : RuntimeDecodeResult)

private def parseAllocationArray (catalog : Reader.Catalog) (values : Array Json) : Except String (Array AllocationNode) := do
  let rawValues ← catalog.array (← catalog.field catalog.root "allocations" "$") "$.allocations"
  unless rawValues.size == values.size do throw "$.allocations: allocation table size mismatch"
  values.mapIdxM fun index value => do
    let path := s!"$.allocations[{index}]"
    let some raw := rawValues[index]? | throw s!"{path}: source allocation absent"
    let kind ← catalog.string (← catalog.field raw "kind" path) path
    let status ← catalog.string (← catalog.field raw "status" path) path
    if kind != "memory" || parseStatus status != .supported then
      return ← parseAllocation value path
    let memory ← catalog.readAllocationMemory raw path
    let id ← catalog.natural (← catalog.field raw "allocation_id" path) path
    let sourceAllocId ← match ← catalog.optionalField raw "source_alloc_id" path with
      | none | some .null => pure none
      | some input =>
        let id ← catalog.natural input path
        if id == 0 || id >= 2^64 then
          throw s!"{path}.source_alloc_id: expected a nonzero u64 rustc allocation identity"
        pure (some (UInt64.ofNat id))
    return {
      id
      sourceAllocId
      status := .supported
      kind := .memory
      memory := some memory
      data := some (.memory memory)
      payload := value
    }

private def parseInstanceArray (values : Array Json) (retainSyntax : Bool) (validatedProbe : String → Bool) : Except String (Array InstanceNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseInstance value s!"$.instances[{index}]" retainSyntax validatedProbe)
    index := index + 1
  pure result

private def parseBodyArray (values : Array Json) (memo : DecodeMemo) (retainSyntax : Bool) (validatedProbe : String → Bool) : Except String (Array Body) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    let fallback := match optionalField value "def_path" with
      | some (.str name) => name
      | _ => s!"body[{index}]"
    result := result.push (← parseBody value s!"$.bodies[{index}]" fallback memo retainSyntax validatedProbe)
    index := index + 1
  pure result

private def parseDocument (input : Json) (runtimeOnly : Bool := false)
    (profile : Options := {}) : Except String ParsedDocument := do
  let catalog ← profileit "decoder.catalog_validation" profile fun _ => Reader.Catalog.parse input
  let producer ← catalog.producer
  let compilerPredicates ← catalog.readPredicateDefinitions
  let (relations, typeRelationTables) ← catalog.readTypeRelations
  let (layoutIds, layoutTable) ← catalog.readTypeLayouts
  let (projectionQueries, layoutTable, projectionTables) ← catalog.readProjectionQueries layoutTable
  let (compilerFacts, compilerFactTables) ← catalog.readCompilerFacts projectionQueries
  let (layoutTable, abiTables) ← catalog.readAbis layoutTable
  for (entry, id) in abiTables.functions.toList.zipIdx do
    if let some (.error reason) := entry then throw s!"function_abis[{id}]: {reason}"
  let j := catalog.root
  let nodes := catalog.nodes
  let traversal := JsonTraversalCache.fromCatalog catalog
  let _ : Reader.JsonFields := catalog.jsonFields
  let memo := profileit "decoder.shared_decode_memo" profile fun _ => sharedDecodeMemo nodes
  if (← fieldString j "schema" "$") != expectedSchema then
    throw s!"$.schema: expected `{expectedSchema}`"
  if (← fieldNat j "schema_version" "$") != expectedSchemaVersion then
    throw s!"$.schema_version: unsupported schema version"
  if let some path := profileit "decoder.dynamic_vtable_scan" profile fun _ =>
      malformedDynamicVtableUpcast? traversal then
    throw s!"{path}: supported dynamic vtable upcast lacks matching compiler cast evidence"
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  let completeness ← field j "completeness" "$"
  let completeStatus ← fieldString completeness "status" "$.completeness"
  if !(← fieldBool completeness "unsupported_payloads_are_explicit" "$.completeness") then
    throw "$.completeness.unsupported_payloads_are_explicit: must be true"
  let typesJson ← arrayField j "types" "$"
  if typesJson.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  let types ← profileit "decoder.types" profile fun _ => catalog.readTypes layoutIds compilerFacts relations
  let allocationsJson ← arrayField j "allocations" "$"
  let allocations ← profileit "decoder.allocations" profile fun _ => parseAllocationArray catalog allocationsJson
  let compilerAllocIdWorld ← profileit "decoder.compiler_alloc_id_world" profile fun _ => do
    match optionalJson j "compiler_alloc_id_world" with
    | none => pure none
    | some value => pure (some (← parseCompilerAllocIdWorld value allocations))
  let instancesJson ← arrayField j "instances" "$"
  let instances ← profileit "decoder.instances" profile fun _ => parseInstanceArray instancesJson false (exactVtableProbeDiagnostic j)
  let selectedScope ← match optionalJson j "selected_scope" with
    | none => pure none
    | some value => pure (some (← parseSelectedScope value "$.selected_scope"))
  let compilerAbiLayoutSchema ← optionalString j "compiler_abi_layout_schema" "$"
  if let some schema := compilerAbiLayoutSchema then
    if schema != expectedCompilerAbiLayoutSchema then
      throw s!"$.compiler_abi_layout_schema: unsupported schema `{schema}`"
    for (entry, id) in abiTables.arguments.toList.zipIdx do
      if let some argument := entry then
        if argument.layoutId.isNone then throw s!"function ABI argument {id} lacks its physical layout"
  let bodiesJson ← arrayField j "bodies" "$"
  if bodiesJson.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  let bodies ← profileit "decoder.bodies" profile fun _ => parseBodyArray bodiesJson memo false (exactVtableProbeDiagnostic j)
  let (bodies, instances, sourceSpans) ← catalog.readSpans abiTables bodies instances
  let (rootSpan, sourceSpans) ← catalog.readRootSpan sourceSpans
  let (mirTables,abiQueries) ← profileit "decoder.mir_tables" profile fun _ =>
    catalog.readMIR types layoutTable abiTables allocations bodies instances
  let (types, vtableTables) ← catalog.readVtables mirTables compilerPredicates types allocations
  profileit "decoder.validate_all_bodies" profile fun _ => catalog.validateBodies
  profileit "decoder.validate_references" profile fun _ =>
    catalog.validateReferences types.size allocations.size instances.size
  let (typedTree?, valueIssues) ← if runtimeOnly then
      let decoded ← profileit "decoder.runtime_value" profile fun _ =>
        decodeRuntimeValue traversal "$" .any .none memo
      pure (none, flattenRuntimeObligations decoded.obligations)
    else
      let typedTree ← decodeValue j "$" .any .none memo
      pure (some typedTree, valueObligations typedTree "$")
  let mut obligations := valueIssues
  obligations := obligations ++ profileit "decoder.extra_semantic_obligations" profile fun _ =>
    extraSemanticObligations j types layoutTable allocations instances abiTables bodies
  let requiredDependencies := profileit "decoder.required_dependencies" profile fun _ =>
    requiredStructuralDependencies j compilerAllocIdWorld.isSome
  obligations := profileit "decoder.prepared_world_readiness" profile fun _ =>
    preparedWorldReadinessObligations obligations compilerAllocIdWorld allocations
      requiredDependencies.allocationIds
  obligations := obligations ++ profileit "decoder.required_instance_obligations" profile fun _ =>
    requiredIdentityOnlyInstanceObligations instances requiredDependencies.instanceIds
  obligations := obligations ++ profileit "decoder.thread_local_obligations" profile fun _ =>
    threadLocalShapeObligations requiredDependencies.threadLocalRefs
  match selectedScope with
  | some scope => obligations := obligations ++ profileit "decoder.selected_scope_obligations" profile fun _ =>
      selectedScopeObligations scope bodies instances
  | none => pure ()
  let unresolved ← arrayField completeness "unresolved_obligations" "$.completeness"
  if completeStatus != "complete" then
    let message := if completeStatus == "incomplete" then
        "exporter marked the graph incomplete; this import cannot form executable input"
      else s!"unrecognized completeness status `{completeStatus}`"
    obligations := obligations.push ⟨"$.completeness.status", message⟩
  for (message, obligationIndex) in unresolved.toList.zipIdx do
    match (inspectJson message).getStr? with
    | .ok text => obligations := obligations.push ⟨s!"$.completeness.unresolved_obligations[{obligationIndex}]", text⟩
    | .error _ => throw s!"$.completeness.unresolved_obligations[{obligationIndex}]: expected string"
  let runtimeTargetDataLayout ← match optionalJson j "runtime_target_data_layout" with
    | none => pure none
    | some evidence => pure (some ({
        status := parseStatus (← fieldString evidence "status" "$.runtime_target_data_layout")
        payload := evidence
        runtime := Reader.TargetLayout.importTarget evidence
      } : TargetDataLayoutEvidence))
  -- Source-shaped generic syntax is an observation, not executable metadata.
  -- The typed allocation-function and vtable tables above own those semantics.
  let allocations := allocations.map (fun node =>
    {node with data := node.data.map fun data => match data with
      | .function source => .function {source with genericArgs := .diagnostic .null}
      | .vtable source => .vtable {source with predicates := #[], entries := #[]}
      | other => other})
  let core : ImportDocumentCore := {
    compilerPredicates := compilerPredicates
    compilerAbiLayoutSchema := compilerAbiLayoutSchema
    producer := producer
    runtimeTargetDataLayout := runtimeTargetDataLayout
    completenessStatus := parseStatus completeStatus
    types := types
    layoutTable := layoutTable
    projectionTables := projectionTables
    typeRelationTables := typeRelationTables
    compilerFactTables := compilerFactTables
    compilerTypeCatalogs := catalog.readPrimitiveTypes
    abiTables := abiTables
    abiQueries := abiQueries
    covarianceQueries := catalog.readCovariance types.size
    vtableTables := vtableTables
    mirTables := mirTables
    allocations := allocations
    compilerAllocIdWorld := compilerAllocIdWorld
    instances := instances
    selectedScope := selectedScope
    bodies := bodies
    sourceSpans := sourceSpans
    rootSpan := rootSpan
    rootSpanDeclared := ((jsonField? j "compiler_session_queries").bind (fun session => jsonField? session "root_span")).isOk
    validatedVtableProbeDiagnostics := (valueIssues.flatMap fun issue => #[issue.path, issue.path ++ ".status"]).filter (exactVtableProbeDiagnostic j)
    obligations := obligations
    raw := j
    sharedNodes := nodes
    compilerValueMemo := none
  }
  AllocIdWorldValidation.validate core
  let requiredLayoutPaths := types.toList.zipIdx.filterMap fun (ty, typeIndex) =>
    if requiredDependencies.typeIds.contains ty.id then some s!"$.types[{typeIndex}].layout.status" else none
  let requiredInstancePaths := instances.toList.zipIdx.foldl (fun paths (instNode, instanceIndex) =>
    if requiredDependencies.instanceIds.contains instNode.id then
      paths ++ #[s!"instances[{instanceIndex}]", s!"$.instances[{instanceIndex}].status"]
    else paths) #[]
  -- Producer-authored paths refer to transport array order, not dense IDs.
  -- Validate those hints against that original root with the catalog reader.
  let retainedRole := @retainedQueryDiagnosticRole catalog.jsonFields catalog.sourceRoot
  let scopeIsSelected := selectedScope.isSome
  let blockingObligations := if scopeIsSelected then
      selectedScopeBlockingObligations j retainedRole obligations requiredLayoutPaths requiredInstancePaths
    else obligations
  let scopeIssuesRemain := !blockingObligations.isEmpty
  let ready :=
    if scopeIsSelected then !scopeIssuesRemain
    else completeStatus == "complete" && obligations.isEmpty
  match typedTree? with
  | some typedTree =>
    let doc := core.withTypedTree typedTree
    let executionInput := if ready then some ⟨doc⟩ else none
    return .full ⟨doc, executionInput, blockingObligations⟩
  | none =>
    let executionInput := if ready then some ⟨core⟩ else none
    return .runtime ⟨core, executionInput, blockingObligations⟩

def decodeJson (text : String) : Except String DecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json with
  | .full result => pure result
  | .runtime _ => throw "internal decoder mode mismatch"

def decodeFile (path : System.FilePath) : IO (Except String DecodeResult) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Runtime decoder with optional Lean profiler options. Profiling wrappers are
kernel identity functions; with profiling disabled this preserves the ordinary
decoder result and diagnostic order. -/
def decodeRuntimeJsonProfiled (text : String) (profile : Options) : Except String RuntimeDecodeResult := do
  let json ← profileit "decoder.json_parse" profile fun _ => Json.parse text
  match ← profileit "decoder.document" profile fun _ => parseDocument json true profile with
  | .runtime result => pure result
  | .full _ => throw "internal decoder mode mismatch"

/-- Runtime-only entry point, preserving validation and diagnostic precedence
without retaining the full typed projection. -/
def decodeRuntimeJson (text : String) : Except String RuntimeDecodeResult :=
  decodeRuntimeJsonProfiled text {}

def decodeRuntimeFile (path : System.FilePath) : IO (Except String RuntimeDecodeResult) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeRuntimeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Typed metadata entrypoints for compiler-query adapters. -/
def decodeAllocationMemoryEvidence (j : Json) : Except String AllocationMemory :=
  parseAllocationMemory j "$allocation"


end Miri.Input
