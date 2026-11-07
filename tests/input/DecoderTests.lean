import Miri.Input

open Lean
open Miri.Input

private def fail (message : String) : IO α := throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else fail message

private def field (catalog : Reader.Catalog) (j : Json) (key : String) : Except String Json := do
  catalog.inspect (← catalog.field j key "fixture") "fixture"

private def array (catalog : Reader.Catalog) (j : Json) : Except String (Array Json) :=
  catalog.array j "fixture"

private def getAt (catalog : Reader.Catalog) (values : Array Json) (index : Nat) : Except String Json :=
  match values[index]? with
  | some value => catalog.inspect value "fixture"
  | none => .error s!"array index {index} is out of range"

private def setField (catalog : Reader.Catalog) (j : Json) (key : String) (value : Json) : Except String Json := do
  match ← catalog.inspect j "fixture" with
  | .obj fields =>
    let retained := fields.toList.filter fun entry => entry.1 != key
    return Json.mkObj ((key, value) :: retained)
  | _ => throw "expected object while replacing field"

private def updateAt (values : Array Json) (index : Nat) (value : Json) : Except String (Array Json) := do
  if index >= values.size then throw s!"array index {index} is out of range"
  let mut out := #[]
  for (old, position) in values.toList.zipIdx do
    out := out.push (if position == index then value else old)
  return out

private partial def replaceFirstField (j : Json) (key : String) (replacement : Json)
    : Except String (Json × Bool) := do
  match j with
  | .arr values =>
    let mut out := #[]
    let mut changed := false
    for value in values do
      if changed then out := out.push value
      else
        let (next, found) ← replaceFirstField value key replacement
        out := out.push next
        changed := found
    return (.arr out, changed)
  | .obj fields =>
    let mut out := #[]
    let mut changed := false
    for (fieldKey, value) in fields.toList do
      if !changed && fieldKey == key then
        out := out.push (fieldKey, replacement)
        changed := true
      else if changed then out := out.push (fieldKey, value)
      else
        let (next, found) ← replaceFirstField value key replacement
        out := out.push (fieldKey, next)
        changed := found
    return (Json.mkObj out.toList, changed)
  | _ => return (j, false)

private def object (fields : List (String × Json)) : Json := Json.mkObj fields
private def number (value : Nat) : Json := toJson value
private def string (value : String) : Json := toJson value

private def rewriteFirstBody (catalog : Reader.Catalog) (doc : Json) (rewrite : Json → Except String Json) : Except String Json := do
  let bodies ← array catalog (← field catalog doc "bodies")
  let first ← getAt catalog bodies 0
  setField catalog doc "bodies" (toJson (← updateAt bodies 0 (← rewrite first)))

private def rewriteFirstBlock (catalog : Reader.Catalog) (body : Json) (rewrite : Json → Except String Json) : Except String Json := do
  let blocks ← array catalog (← field catalog body "basic_blocks")
  let first ← getAt catalog blocks 0
  setField catalog body "basic_blocks" (toJson (← updateAt blocks 0 (← rewrite first)))

private def rewriteFirstTerminator (catalog : Reader.Catalog) (block : Json) (rewrite : Json → Except String Json) : Except String Json := do
  let term ← field catalog block "terminator"
  setField catalog block "terminator" (← rewrite term)

private def malformedResult (json : Json) : Bool :=
  match decodeJson json.compress with
  | .error _ => true
  | .ok _ => false

private partial def containsBinary (wanted : Miri.MIR.BinOp) : TypedValue → Bool
  | .binOperator actual _ => actual == wanted
  | .array values => values.any (containsBinary wanted)
  | .object fields => fields.any fun (_, value) => containsBinary wanted value
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields => fields.any fun (_, value) => containsBinary wanted value
  | _ => false

private partial def containsUnary (wanted : Miri.MIR.UnOp) : TypedValue → Bool
  | .unOperator actual _ => actual == wanted
  | .array values => values.any (containsUnary wanted)
  | .object fields => fields.any fun (_, value) => containsUnary wanted value
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields => fields.any fun (_, value) => containsUnary wanted value
  | _ => false

private partial def containsEnumTag (wanted : TypedEnumTag) : TypedValue → Bool
  | .enumTag category _ fields => category == wanted || fields.any fun (_, value) => containsEnumTag wanted value
  | .array values => values.any (containsEnumTag wanted)
  | .object fields => fields.any fun (_, value) => containsEnumTag wanted value
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields => fields.any fun (_, value) => containsEnumTag wanted value
  | _ => false

private partial def containsUserTypeProjection : TypedValue → Bool
  | .userTypeProjection _ => true
  | .array values => values.any containsUserTypeProjection
  | .object fields => fields.any fun (_, value) => containsUserTypeProjection value
  | .enumTag _ _ fields => fields.any fun (_, value) => containsUserTypeProjection value
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields => fields.any fun (_, value) => containsUserTypeProjection value
  | _ => false

private partial def hasTypedUserTypeProjection : TypedValue → Bool
  | .userTypeProjection value =>
    value.baseIndex == some 2 && value.projections == some #[
      .deref, .field 1, .index, .constantIndex 2 4 true, .subslice 1 2 false,
      .downcast none 3, .opaqueCast, .unwrapUnsafeBinder, .phantomDeref]
  | .array values => values.any hasTypedUserTypeProjection
  | .object fields => fields.any fun (_, value) => hasTypedUserTypeProjection value
  | .enumTag _ _ fields => fields.any fun (_, value) => hasTypedUserTypeProjection value
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields => fields.any fun (_, value) => hasTypedUserTypeProjection value
  | _ => false

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => fail message

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | value :: _ => pure value
    | [] => fail "usage: DecoderTests <schema-v3-export.json>"
  let source ← IO.FS.readFile path
  let original ← match Json.parse source with
    | .ok value => pure value
    | .error error => fail s!"invalid fixture JSON: {error}"
  let catalog ← must (Reader.Catalog.parse original)

  let decoded ← match decodeJson source with
    | .ok value => pure value
    | .error error => fail s!"valid fixture rejected: {error}"
  let document := decoded.document
  check (document.producer.miriCommit == expectedMiriCommit) "wrong Miri pin in decoded document"
  check (document.producer.rustcCommit == expectedRustcCommit) "wrong rustc pin in decoded document"
  check (!document.bodies.isEmpty && !document.types.isEmpty) "typed body/type graph is empty"
  check decoded.executionInput.isNone "incomplete exporter graph became executable input"
  check (document.instances.any fun inst => inst.body.isSome) "instance MIR body was not decoded into typed Body"
  check (document.instances.any fun inst => inst.kind == .instanceMir && inst.bodyInstantiation.isSome &&
      inst.instanceArgsAreMonomorphic == some true)
    "substituted instance body metadata was not decoded"
  check (document.bodies.any fun body => body.promotedBodies.any fun promoted => promoted.body.isSome)
    "promoted MIR bodies were not decoded into typed body cores"
  check (containsBinary .Lt document.typedTree) "binary operator did not use the canonical BinOp type"
  check (containsBinary .AddWithOverflow document.typedTree) "overflowing binary operator was not typed"
  check (containsUnary .Not document.typedTree) "unary operator did not use the canonical UnOp type"
  check (containsEnumTag .borrowKind document.typedTree) "borrow kinds were not decoded as typed enum tags"
  check (containsEnumTag .safety document.typedTree) "function safety tags were not retained as typed values"
  check (document.allocations.any fun node => node.memory.isSome) "structured allocation memory was not decoded"
  check (document.allocations.any fun node => match node.data with | some (.static _) => true | _ => false)
    "static initializer allocation metadata was not decoded"
  check (document.vtableTables.entryLists.any fun slot => slot.any (fun entries => !entries.isEmpty))
    "vtable entry metadata was not decoded"
  check (document.mirTables.functionTypes.any fun record => match record with | .ok (some _) => true | _ => false) "function type signature metadata was not decoded"
  check (document.types.any fun node => node.shapeMetadata.signedKind == some (.known .isize))
    "signed integer name was not decoded to the canonical IntegerKind"
  check (document.types.any fun node => node.shapeMetadata.unsignedKind == some (.known .u32))
    "unsigned integer name was not decoded to the canonical IntegerKind"
  check (document.types.any fun node => node.shapeMetadata.floatKind == some .f32)
    "float name was not decoded to the pinned float tag"
  check (document.types.any fun node => node.shapeMetadata.adtKind == some .enumKind)
    "enum ADT name was not decoded to its typed tag"
  let abis := document.abiTables.functions.filterMap (fun entry => entry.bind (·.toOption))
  check (!abis.isEmpty && abis.all fun abi => match abi.callingConvention.kind with | .unknown _ => false | _ => true)
    "function ABI calling convention was not decoded to a known enum"
  check (document.types.any fun node => match (document.layoutTable.lookup node.layoutId).toOption.bind (·.variantsLayout) with
    | some variants => variants.tagEncoding.isSome
    | none => false) "structured variant tag-encoding metadata was not decoded"
  check (document.obligations.any fun item => item.path == "$.completeness.status") "incomplete top-level status did not become an obligation"
  for allocation in document.allocations do
    match allocation.memory with
    | none => pure ()
    | some memory =>
      for relocation in memory.relocations do
        let (allocId, immutable, sharedRef) := relocation.ctfeProvenance.intoParts
        let expectedId := Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat (relocation.target + 1))
        check (expectedId == some allocId && immutable == relocation.immutable && sharedRef == relocation.sharedRef)
          "allocation relocation lost its reversible CTFE provenance identity"

  let badVersion ← must (setField catalog original "schema_version" (number 999))
  check (malformedResult badVersion) "unsupported schema version was accepted"

  let syntheticFunction := object [
    ("allocation_id", number document.allocations.size),
    ("status", string "supported"),
    ("kind", string "function"),
    ("instance_id", number 0),
    ("instance_def_id", object [("crate", number 0), ("index", number 7)]),
    ("instance_def_path", string "fixture::root"),
    ("generic_args", toJson (#[] : Array Json))]
  let syntheticTypeId := object [
    ("allocation_id", number (document.allocations.size + 1)),
    ("status", string "supported"),
    ("kind", string "type_id"),
    ("type", object [("type_id", number 0)])]
  let allocations ← must (array catalog (← must (field catalog original "allocations")))
  let expandedAllocations := allocations.push syntheticFunction |>.push syntheticTypeId
  let withSyntheticAllocations ← must (setField catalog original "allocations" (toJson expandedAllocations))
  let allocationDataTest ← match decodeJson withSyntheticAllocations.compress with
    | .ok result => pure result
    | .error error => fail s!"typed function/type-id allocation payloads were rejected: {error}"
  check (allocationDataTest.document.allocations.any fun node => match node.data with | some (.function _) => true | _ => false)
    "function allocation was not decoded into typed metadata"
  check (allocationDataTest.document.allocations.any fun node => match node.data with | some (.typeId _) => true | _ => false)
    "type-id allocation was not decoded into typed metadata"

  let unknownBorrow ← must <| do
    let replacement := object [("kind", string "future_borrow_kind"), ("status", string "supported")]
    let (changed, found) ← replaceFirstField original "borrow_kind" replacement
    if !found then throw "fixture does not contain a borrow_kind tag"
    pure changed
  -- Current typed MIR import rejects unknown executable variants before a
  -- document is returned; diagnostic-only paths may still record obligations.
  match decodeJson unknownBorrow.compress with
  | .error error =>
    check (error.contains "unsupported borrow kind future_borrow_kind")
      s!"unknown borrow rejected for an unrelated reason: {error}"
  | .ok result =>
    check (result.document.obligations.any fun item => item.message.contains "future_borrow_kind")
      "unknown nested BorrowKind was silently accepted"

  let unknownSafety ← must <| do
    let replacement := object [("kind", string "future_safety"), ("status", string "supported")]
    let (changed, found) ← replaceFirstField original "safety" replacement
    if !found then throw "fixture does not contain a safety tag"
    pure changed
  let unknownSafetyResult ← match decodeJson unknownSafety.compress with
    | .ok result => pure result
    | .error error => fail s!"unknown function safety tag should remain an obligation: {error}"
  check (unknownSafetyResult.document.obligations.any fun item => item.message.contains "future_safety")
    "unknown function safety was silently accepted"

  let incompleteCanonicalAbi ← must <| do
    let replacement := object [("kind", string "arm"), ("status", string "supported")]
    let (changed, found) ← replaceFirstField original "calling_convention" replacement
    if !found then throw "fixture does not contain a canonical calling convention"
    pure changed
  let incompleteCanonicalResult ← match decodeJson incompleteCanonicalAbi.compress with
    | .ok result => pure result
    | .error error => fail s!"missing ABI subkind should remain an obligation: {error}"
  check (incompleteCanonicalResult.document.obligations.any fun item => item.path.endsWith ".arm_call")
    "ARM calling convention without its call kind was treated as complete"

  let nicheTypeIndex := document.types.toList.findIdx? (fun node =>
    match (document.layoutTable.lookup node.layoutId).toOption.bind (·.variantsLayout) with
    | some variants => variants.tagEncoding.isSome
    | none => false)
  match nicheTypeIndex with
  | some index =>
    let badTagEncoding ← must <| do
      let types ← array catalog (← field catalog original "types")
      let typeNode ← getAt catalog types index
      let layout ← field catalog typeNode "layout"
      let variants ← field catalog layout "variants"
      let encoding ← field catalog variants "tag_encoding"
      let corrupt ← setField catalog encoding "niche_start" (string "not-a-number")
      let variants ← setField catalog variants "tag_encoding" corrupt
      let layout ← setField catalog layout "variants" variants
      let typeNode ← setField catalog typeNode "layout" layout
      setField catalog original "types" (toJson (← updateAt types index typeNode))
    check (malformedResult badTagEncoding) "malformed u128 niche encoding was accepted"
  | none => fail "fixture did not exercise a structured tag encoding"

  let badRelocation ← must <| do
    let (changed, found) ← replaceFirstField original "storage_offset_bytes" (number 999999)
    if !found then throw "fixture does not contain a relocation"
    pure changed
  check (malformedResult badRelocation) "relocation bytes outside the allocation were accepted"

  let producer ← must (field catalog original "producer")
  let badProducer ← must (setField catalog producer "rustc_commit" (string "not-the-pinned-rustc"))
  let badPin ← must (setField catalog original "producer" badProducer)
  check (malformedResult badPin) "wrong rustc pin was accepted"

  let danglingType ← must (setField catalog original "synthetic_type_ref" (object [("type_id", number 999999)]))
  check (malformedResult danglingType) "dangling type reference was accepted"
  let danglingAlloc ← must (setField catalog original "synthetic_allocation_ref" (object [("allocation_id", number 999999)]))
  check (malformedResult danglingAlloc) "dangling allocation reference was accepted"

  let typesJson ← must (field catalog original "types")
  let types ← must (array catalog typesJson)
  let secondType ← must (getAt catalog types 1)
  let duplicateType ← must (setField catalog secondType "type_id" (number 0))
  let duplicateTypes ← must (updateAt types 1 duplicateType)
  let duplicateId ← must (setField catalog original "types" (toJson duplicateTypes))
  check (malformedResult duplicateId) "duplicate graph-node ID was accepted"

  let allocationsJson ← must (field catalog original "allocations")
  let allocations ← must (array catalog allocationsJson)
  let firstAllocation ← must (getAt catalog allocations 0)
  let duplicateAllocation ← must (setField catalog firstAllocation "allocation_id" (number 1))
  let duplicateAllocations ← must (updateAt allocations 0 duplicateAllocation)
  let duplicateAllocationId ← must (setField catalog original "allocations" (toJson duplicateAllocations))
  check (malformedResult duplicateAllocationId) "duplicate allocation ID was accepted"

  let instancesJson ← must (field catalog original "instances")
  let instances ← must (array catalog instancesJson)
  let secondInstance ← must (getAt catalog instances 1)
  let duplicateInstance ← must (setField catalog secondInstance "instance_id" (number 0))
  let duplicateInstances ← must (updateAt instances 1 duplicateInstance)
  let duplicateInstanceId ← must (setField catalog original "instances" (toJson duplicateInstances))
  check (malformedResult duplicateInstanceId) "duplicate instance ID was accepted"

  let danglingInstance ← must (setField catalog original "synthetic_instance_ref" (object [("instance_id", number 999999)]))
  check (malformedResult danglingInstance) "dangling instance reference was accepted"

  let badLocal ← must <| rewriteFirstBody catalog original fun body => do
    let locals ← array catalog (← field catalog body "locals")
    let firstLocal ← getAt catalog locals 0
    let changed ← setField catalog firstLocal "local" (number 999999)
    setField catalog body "locals" (toJson (← updateAt locals 0 changed))
  check (malformedResult badLocal) "out-of-range local declaration was accepted"

  let badLocalReference ← must <| rewriteFirstBody catalog original fun body =>
    rewriteFirstBlock catalog body fun block =>
      rewriteFirstTerminator catalog block fun terminator => do
        let kind ← field catalog terminator "kind"
        let changed ← setField catalog kind "local" (number 999999)
        setField catalog terminator "kind" changed
  check (malformedResult badLocalReference) "out-of-range local reference was accepted"

  let badEdge ← must <| rewriteFirstBody catalog original fun body =>
    rewriteFirstBlock catalog body fun block =>
      rewriteFirstTerminator catalog block fun terminator => do
        let badKind := object [("variant", string "Goto"), ("status", string "supported"), ("target", number 999999)]
        setField catalog terminator "kind" badKind
  check (malformedResult badEdge) "out-of-range basic-block edge was accepted"

  let badProjection ← must <| rewriteFirstBody catalog original fun body =>
    rewriteFirstBlock catalog body fun block =>
      rewriteFirstTerminator catalog block fun terminator => do
        let kind ← field catalog terminator "kind"
        let withProjection ← setField catalog kind "synthetic_place" (object [("projection", toJson #[object [("kind", string "Field"), ("index", number 0)]])])
        setField catalog terminator "kind" withProjection
  check (malformedResult badProjection) "incomplete projection payload was accepted"

  let futureVariant ← must <| rewriteFirstBody catalog original fun body =>
    rewriteFirstBlock catalog body fun block =>
      rewriteFirstTerminator catalog block fun terminator => do
        let future := object [("variant", string "NewPinnedVariant"), ("status", string "supported")]
        setField catalog terminator "kind" future
  match decodeJson futureVariant.compress with
  | .error error =>
    check (error.contains "unsupported terminator variant NewPinnedVariant")
      s!"future terminator rejected for an unrelated reason: {error}"
  | .ok result =>
    check result.executionInput.isNone "unknown MIR variant became executable"
    check (result.document.obligations.any fun item => item.message.contains "NewPinnedVariant")
      "unknown MIR variant did not produce an explicit obligation"

  let completion ← must (field catalog original "completeness")
  let completion ← must (setField catalog completion "status" (string "complete"))
  let completion ← must (setField catalog completion "unresolved_obligations" (toJson (#[] : Array Json)))
  let falselyComplete ← must (setField catalog original "completeness" completion)
  let falseResult ← match decodeJson falselyComplete.compress with
    | .ok value => pure value
    | .error error => fail s!"status-label check input rejected structurally: {error}"
  check falseResult.executionInput.isNone
    "exporter completeness label erased unsupported/unknown semantic payload obligations"

  let supported := string "supported"
  let typedTagProbe := object [
    ("phase", object [("status", supported), ("kind", string "runtime"),
      ("phase", object [("status", supported), ("kind", string "optimized")])]),
    ("retag", object [("status", supported), ("kind", string "yes"), ("performs_retag", Json.bool true)]),
    ("runtime_checks", object [("status", supported), ("kind", string "RuntimeChecks"),
      ("check", object [("status", supported), ("kind", string "overflow_checks"), ("enabled", Json.bool true)])]),
    ("fake_read", object [("variant", string "FakeRead"), ("status", supported),
      ("cause", object [("status", supported), ("kind", string "matched_place"), ("hoisted_from", Json.null)])]),
    ("call", object [("variant", string "Call"), ("status", supported),
      ("call_source", object [("status", supported), ("kind", string "normal_call")])]),
    ("drop", object [("variant", string "BackwardIncompatibleDropHint"), ("status", supported),
      ("reason", object [("status", supported), ("kind", string "edition_2024")])]),
    ("region", object [("status", supported), ("kind", string "bound"),
      ("index_kind", object [("kind", string "bound"), ("debruijn_index", number 0)]),
      ("variable_index", number 0),
      ("bound_kind", object [("status", supported), ("kind", string "anonymous")])]),
    ("unsupported_region", object [("status", string "unsupported"),
      ("kind", string "inference_variable"), ("index", number 3)]),
    ("borrow_kind", object [
      ("status", supported), ("kind", string "fake"), ("fake_kind", string "shallow"),
      ("retag_mode", string "default")]),
    ("ascribe_statement", object [
      ("variant", string "AscribeUserType"), ("status", supported),
      ("place", object [("local", number 0), ("projection", toJson (#[] : Array Json))]),
      ("user_type_projection", object [
        ("status", supported), ("base_index", number 2),
        ("projections", toJson #[
          object [("kind", string "Deref")],
          object [("kind", string "Field"), ("index", number 1)],
          object [("kind", string "Index")],
          object [("kind", string "ConstantIndex"), ("offset", number 2),
            ("min_length", number 4), ("from_end", Json.bool true)],
          object [("kind", string "Subslice"), ("from", number 1), ("to", number 2),
            ("from_end", Json.bool false)],
          object [("kind", string "Downcast"), ("name", Json.null), ("variant_index", number 3)],
          object [("kind", string "OpaqueCast")],
          object [("kind", string "UnwrapUnsafeBinder")],
          object [("kind", string "PhantomDeref")]])]),
      ("variance", object [("status", supported), ("kind", string "invariant")])]),
    ("coverage_statement", object [
      ("variant", string "Coverage"), ("status", supported),
      ("coverage", object [
        ("status", supported), ("kind", string "point"), ("point_kind", string "expr"),
        ("hir_id", object [("owner_def_id", string "0:1"), ("local_id", number 7)])])]),
    ("binary", object [("kind", string "BinaryOp"), ("status", supported),
      ("operator", object [("status", supported), ("kind", string "add")])]),
    ("unary", object [("kind", string "UnaryOp"), ("status", supported),
      ("operator", object [("status", supported), ("kind", string "not")])])]
  let taggedInput ← must (setField catalog original "typed_tag_probe" typedTagProbe)
  let taggedResult ← match decodeJson taggedInput.compress with
    | .ok result => pure result
    | .error error => fail s!"known pinned MIR tags were rejected: {error}"
  for category in [.mirPhase, .mirPhaseStage, .withRetag, .runtimeCheck,
      .fakeReadCause, .callSource, .backwardDropReason, .regionKind,
      .boundRegionKind, .boundVarIndexKind, .variance, .coverageKind,
      .coveragePointKind, .fakeBorrowRetagMode] do
    check (containsEnumTag category taggedResult.document.typedTree)
      "MIR tag family was not preserved as a typed value"
  check (containsUserTypeProjection taggedResult.document.typedTree)
    "AscribeUserType projection wrapper was not decoded to its dedicated typed record"
  check (hasTypedUserTypeProjection taggedResult.document.typedTree)
    "AscribeUserType projection variants or payload fields were not preserved exactly"
  check (containsBinary .Add taggedResult.document.typedTree)
    "tagged lower-snake binary operator did not map to canonical BinOp"
  check (taggedResult.document.obligations.any fun item => item.path.contains "unsupported_region")
    "unsupported region variable was silently treated as supported"

  let malformedUserTypeProjection ← must <| do
    let (changed, found) ← replaceFirstField taggedInput "base_index" (string "not-an-index")
    if !found then throw "typed tag probe lost its user-type projection base index"
    pure changed
  check (malformedResult malformedUserTypeProjection)
    "malformed user-type projection annotation index was accepted"

  let unknownCoverageTag ← must <| do
    let coverage ← field catalog taggedInput "typed_tag_probe"
    let future := object [
      ("variant", string "Coverage"), ("status", supported),
      ("coverage", object [("status", supported), ("kind", string "future_coverage_kind")])]
    let changedProbe ← setField catalog coverage "coverage_statement" future
    setField catalog taggedInput "typed_tag_probe" changedProbe
  let unknownCoverageResult ← match decodeJson unknownCoverageTag.compress with
    | .ok result => pure result
    | .error error => fail s!"unknown coverage tag should remain an obligation: {error}"
  check (unknownCoverageResult.document.obligations.any fun item => item.message.contains "future_coverage_kind")
    "unknown CoverageKind was silently accepted"

  let unsupportedOperator ← must <| do
    let replacement := object [("status", string "unsupported"), ("kind", string "add")]
    let (changed, found) ← replaceFirstField taggedInput "operator" replacement
    if !found then throw "typed tag probe lost its binary operator"
    pure changed
  match decodeJson unsupportedOperator.compress with
  | .error error =>
    check (error.contains "unsupported unary operator" || error.contains "unsupported binary operator")
      s!"unsupported operator rejected for an unrelated reason: {error}"
  | .ok result =>
    check (result.document.obligations.any fun item =>
      item.path.endsWith ".operator" && item.message.contains "unsupported")
      "unsupported tagged binary operator status was dropped"

  let inconsistentRetag ← must <| do
    let (changed, found) ← replaceFirstField taggedInput "performs_retag" (Json.bool false)
    if !found then throw "typed tag probe lost its WithRetag witness"
    pure changed
  let inconsistentRetagResult ← match decodeJson inconsistentRetag.compress with
    | .ok result => pure result
    | .error error => fail s!"inconsistent WithRetag witness should remain an obligation: {error}"
  check (inconsistentRetagResult.document.obligations.any fun item => item.message.contains "disagrees with the WithRetag")
    "mismatched WithRetag witness was accepted"

  let unknownIntegerType ← must <| do
    let (changed, found) ← replaceFirstField original "signed_kind" (string "i256")
    if !found then throw "fixture does not contain a signed integer kind"
    pure changed
  let unknownIntegerTypeResult ← match decodeJson unknownIntegerType.compress with
    | .ok result => pure result
    | .error error => fail s!"unknown integer type should remain an obligation: {error}"
  check (unknownIntegerTypeResult.document.obligations.any fun item => item.message.contains "i256")
    "unknown integer type tag was silently accepted"

  let contradictoryIntegerType ← must <| do
    let (changed, found) ← replaceFirstField original "signed_kind" (string "u8")
    if !found then throw "fixture does not contain a signed integer kind"
    pure changed
  let contradictoryIntegerTypeResult ← match decodeJson contradictoryIntegerType.compress with
    | .ok result => pure result
    | .error error => fail s!"well-formed but contradictory integer metadata was rejected: {error}"
  check (contradictoryIntegerTypeResult.document.obligations.any fun item =>
      item.message.contains "unsigned integer kind")
    "signed integer shape accepted a contradictory unsigned IntegerKind"

  let missingRuntimeCheckWitness ← must <| do
    -- Target the MIR witness, independently of compiler session catalogs
    -- which also contain source `enabled` booleans.
    let probe ← field catalog taggedInput "typed_tag_probe"
    let operand ← field catalog probe "runtime_checks"
    let witness ← field catalog operand "check"
    let witness ← setField catalog witness "enabled" Json.null
    let operand ← setField catalog operand "check" witness
    let probe ← setField catalog probe "runtime_checks" operand
    setField catalog taggedInput "typed_tag_probe" probe
  let missingRuntimeCheckResult ← match decodeJson missingRuntimeCheckWitness.compress with
    | .ok result => pure result
    | .error error => fail s!"malformed RuntimeChecks witness should remain an obligation: {error}"
  check (missingRuntimeCheckResult.document.obligations.any fun item =>
      item.path.contains "typed_tag_probe.runtime_checks.check" && item.path.endsWith ".enabled")
    "missing runtime-check boolean was treated as complete"

  let firstBody ← must (getAt catalog (← must (array catalog (← must (field catalog original "bodies")))) 0)
  let rootPath ← must (field catalog firstBody "def_path")
  let rootId ← must (field catalog firstBody "def_id")
  let rootedScope := object [
    ("kind", string "rooted_structural_closure"),
    ("status", string "complete"),
    ("semantics", string "structural_export_closure_only"),
    ("roots", toJson #[object [("def_path", rootPath), ("def_id", rootId)]]),
    ("unresolved_obligations", toJson (#[] : Array Json))]
  let scopedButIncompleteGraph ← must (setField catalog original "selected_scope" rootedScope)
  let scopedResult ← match decodeJson scopedButIncompleteGraph.compress with
    | .ok result => pure result
    | .error error => fail s!"well-shaped selected scope was rejected: {error}"
  check scopedResult.document.selectedScope.isSome "selected structural scope was not retained"
  check scopedResult.executionInput.isNone
    "a complete selected-scope label erased unsupported records still present in the scoped graph"
  check (scopedResult.document.obligations.any fun item => item.path == "$.completeness.status")
    "scoped import dropped global completeness obligations from the document"

  let readySource ← IO.FS.readFile "examples/empty_function/input.json"
  let ready ← must (Json.parse readySource)
  let readyCatalog ← must (Reader.Catalog.parse ready)
  let completion ← must (field readyCatalog ready "completeness")
  let completion ← must (setField readyCatalog completion "status" (string "incomplete"))
  let completion ← must (setField readyCatalog completion "unresolved_obligations"
    (toJson #[string "unrelated global root is incomplete"]))
  let withGlobalNote ← must (setField readyCatalog ready "completeness" completion)
  let scopedReady ← match decodeJson withGlobalNote.compress with
    | .ok result => pure result
    | .error error => fail s!"complete compiler-produced selected closure was rejected: {error}"
  check scopedReady.executionInput.isSome
    "globally incomplete notes incorrectly blocked a checked selected closure"
  check (scopedReady.document.obligations.any fun item => item.message.contains "unrelated global root")
    "scoped input discarded unrelated global obligations from its source document"

  IO.println s!"input decoder tests passed: bodies={document.bodies.size}, instance_bodies={document.instances.filter (·.body.isSome) |>.size}, types={document.types.size}, obligations={document.obligations.size}"
  return 0
