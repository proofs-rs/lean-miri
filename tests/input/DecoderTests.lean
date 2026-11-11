import MiriTests.Input.JsonFixtures
import Miri.Input.Decoder

open Lean
open Miri.Input
open Miri.Input.DecoderValues

private def fail (message : String) : IO α := throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else fail message

private def string (value : String) : String := Json.renderString value
private def object (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (key,value) => string key ++ ":" ++ value) ++ "}"
private def number (value : Nat) : String := toString value
private def encodeArray (values : Array String) := "[" ++ String.intercalate "," values.toList ++ "]"
private def getField (source key : String) : Except String String := do
  return (← (← JsonFixtures.parse source).field key).text
private def array (source : String) : Except String (Array String) := do
  return (← (← JsonFixtures.parse source).array).map (·.text)
private def getAt (values : Array α) (index : Nat) : Except String α :=
  match values[index]? with | some value => .ok value | none => .error s!"array index {index} is out of range"
private def setField (source key value : String) : Except String String := do
  let fields ← (← JsonFixtures.parse source).object
  let retained := fields.filterMap fun (name, child) => if name == key then none else some (name,child.text)
  pure (object ((key,value)::retained.toList))
private def updateAt (values : Array String) (index : Nat) (value : String) : Except String (Array String) := do
  if index >= values.size then throw s!"array index {index} is out of range"
  pure (values.set! index value)
private partial def replaceFirstField (source key replacement : String) : Except String (String × Bool) := do
  let node ← JsonFixtures.parse source
  if let .ok values := node.array then
    let mut out := #[]
    let mut changed := false
    for value in values do
      if changed then out := out.push value.text
      else
        let (next,found) ← replaceFirstField value.text key replacement
        out := out.push next
        changed := found
    return (encodeArray out,changed)
  if let .ok fields := node.object then
    let mut out := []
    let mut changed := false
    for (name,value) in fields do
      if !changed && name == key then
        out := out ++ [(name,replacement)]
        changed := true
      else if changed then out := out ++ [(name,value.text)]
      else
        let (next,found) ← replaceFirstField value.text key replacement
        out := out ++ [(name,next)]
        changed := found
    return (object out,changed)
  return (source,false)

private def rewriteFirstBody (doc : String) (rewrite : String → Except String String) : Except String String := do
  let bodies ← array (← getField doc "bodies")
  let first ← getAt bodies 0
  setField doc "bodies" (encodeArray (← updateAt bodies 0 (← rewrite first)))

private def rewriteFirstBlock (body : String) (rewrite : String → Except String String) : Except String String := do
  let blocks ← array (← getField body "basic_blocks")
  let first ← getAt blocks 0
  setField body "basic_blocks" (encodeArray (← updateAt blocks 0 (← rewrite first)))

private def rewriteFirstTerminator (block : String) (rewrite : String → Except String String) : Except String String := do
  let term ← getField block "terminator"
  setField block "terminator" (← rewrite term)

private def malformedResult (json : String) : Bool :=
  match decodeJson json with
  | .error _ => true
  | .ok _ => false

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => fail message

private def rvalues (document : ImportDocument) : Array Miri.MIR.Rvalue :=
  document.bodies.flatMap fun body => body.mir.basicBlocks.flatMap fun block =>
    block.statements.filterMap fun statement => match statement.kind with
      | .Assign _ value => some value | _ => none

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | value :: _ => pure value
    | [] => fail "usage: DecoderTests <schema-v7-export.json>"
  let source ← IO.FS.readFile path
  let _ ← must (JsonFixtures.parse source)
  let original := source

  let decoded ← match decodeJson source with
    | .ok value => pure value
    | .error error => fail s!"valid fixture rejected: {error}"
  let document := decoded.document
  check (document.producer.miriCommit == expectedMiriCommit) "wrong Miri pin in decoded document"
  check (document.producer.rustcCommit == expectedRustcCommit) "wrong rustc pin in decoded document"
  check (!document.bodies.isEmpty && !document.types.isEmpty) "typed body/type graph is empty"
  check (document.instances.any fun inst => inst.bodyId.isSome) "instance MIR body was not decoded into typed Body"
  check (document.instances.any fun inst => inst.kind == .instanceMir &&
      inst.bodyId.any (fun id => (document.bodies[id]?).any (·.instanceId == inst.id)))
    "resolved instance does not identify its executable body"
  check (document.bodyRoots.any fun body => body.promotedBodies.any fun promoted => promoted.bodyId.isSome)
    "promoted MIR bodies were not decoded into typed body cores"
  check ((rvalues document).any fun value => match value with | .BinaryOp .Lt .. => true | _ => false) "binary operator did not use the canonical BinOp type"
  check ((rvalues document).any fun value => match value with | .BinaryOp .AddWithOverflow .. => true | _ => false) "overflowing binary operator was not typed"
  check ((rvalues document).any fun value => match value with | .UnaryOp .Not .. => true | _ => false) "unary operator did not use the canonical UnOp type"
  check ((rvalues document).any fun value => match value with | .Ref .. => true | _ => false) "borrow kinds were not decoded into MIR"
  check (document.types.any fun node => node.signature.any fun signature =>
    signature.safety == .Safe || signature.safety == .Unsafe) "function safety tags were not retained as typed values"
  check (document.allocations.any fun node => node.memory.isSome) "structured allocation memory was not decoded"
  check (document.allocations.any fun node => match node.data with | some (.static _) => true | _ => false)
    "static initializer allocation metadata was not decoded"
  check (document.allocations.any fun node => match node.data with | some (.vtable value) => !value.entries.isEmpty | _ => false)
    "vtable entry metadata was not decoded"
  check (document.types.any fun node => node.signature.isSome) "function type signature metadata was not decoded"
  check (document.types.any fun node => node.shapeMetadata.signedKind == some (.known .isize))
    "signed integer name was not decoded to the canonical IntegerKind"
  check (document.types.any fun node => node.shapeMetadata.unsignedKind == some (.known .u32))
    "unsigned integer name was not decoded to the canonical IntegerKind"
  check (document.types.any fun node => node.shapeMetadata.floatKind == some .f32)
    "float name was not decoded to the pinned float tag"
  check (document.types.any fun node => node.shapeMetadata.adtKind == some .enumKind)
    "enum ADT name was not decoded to its typed tag"
  check (!document.functionAbis.isEmpty)
    "function ABI calling convention was not decoded to a known enum"
  check (document.layouts.any fun node => match node.variantsLayout with
    | some variants => variants.tagEncoding.isSome
    | none => false) "structured variant tag-encoding metadata was not decoded"
  for allocation in document.allocations do
    match allocation.memory with
    | none => pure ()
    | some memory =>
      for relocation in memory.relocations do
        let (allocId, immutable, sharedRef) := relocation.ctfeProvenance.intoParts
        let expectedId := Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat (relocation.target + 1))
        check (expectedId == some allocId && immutable == relocation.immutable && sharedRef == relocation.sharedRef)
          "allocation relocation lost its reversible CTFE provenance identity"

  let badVersion ← must (setField original "schema_version" (number 999))
  check (malformedResult badVersion) "unsupported schema version was accepted"

  let syntheticFunction := object [
    ("identities", "[[" ++ number document.allocations.size ++ ",18446744073709551614]]"),
    ("kind", string "function"),
    ("instance_id", number 0)]
  let syntheticTypeId := object [
    ("allocation_id", number (document.allocations.size + 1)),
    ("source_alloc_id", number 18446744073709551615),
    ("kind", string "type_id"),
    ("type", number 0)]
  let allocations ← must (array (← must (getField original "allocations")))
  let expandedAllocations := allocations.push syntheticFunction |>.push syntheticTypeId
  let withSyntheticAllocations ← must (setField original "allocations" (encodeArray expandedAllocations))
  let allocationDataTest ← match decodeJson withSyntheticAllocations with
    | .ok result => pure result
    | .error error => fail s!"typed function/type-id allocation payloads were rejected: {error}"
  check (allocationDataTest.document.allocations.any fun node => match node.data with | some (.function _) => true | _ => false)
    "function allocation was not decoded into typed metadata"
  check (allocationDataTest.document.allocations.any fun node => match node.data with | some (.typeId _) => true | _ => false)
    "type-id allocation was not decoded into typed metadata"

  let unknownBorrow ← must <| do
    let replacement := object [("kind", string "future_borrow_kind")]
    let (changed, found) ← replaceFirstField original "borrow_kind" replacement
    if !found then throw "fixture does not contain a borrow_kind tag"
    pure changed
  check (malformedResult unknownBorrow) "unknownBorrow: failed input was accepted"

  let unknownSafety ← must <| do
    let some index := document.types.toList.findIdx? (·.signature.isSome)
      | throw "fixture does not contain a typed function signature"
    let types ← array (← getField original "types")
    let node ← getAt types index
    let shape ← getField node "shape"
    let signature ← getField shape "signature"
    let signature ← setField signature "safety" (object [("kind", string "future_safety")])
    let shape ← setField shape "signature" signature
    let node ← setField node "shape" shape
    setField original "types" (encodeArray (← updateAt types index node))
  check (malformedResult unknownSafety) "unknown function safety was accepted"

  let incompleteCanonicalAbi ← must <| do
    let replacement := object [("kind", string "arm")]
    let (changed, found) ← replaceFirstField original "calling_convention" replacement
    if !found then throw "fixture does not contain a canonical calling convention"
    pure changed
  check (malformedResult incompleteCanonicalAbi) "incompleteCanonicalAbi: failed input was accepted"

  let nicheTypeIndex := document.layouts.toList.findIdx? (fun node =>
    match node.variantsLayout with
    | some variants => variants.tagEncoding.isSome
    | none => false)
  match nicheTypeIndex with
  | some index =>
    let badTagEncoding ← must <| do
      let layouts ← array (← getField original "layouts")
      let layout ← getAt layouts index
      let variants ← getField layout "variants"
      let encoding ← getField variants "tag_encoding"
      let corrupt ← setField encoding "niche_start" (string "not-a-number")
      let variants ← setField variants "tag_encoding" corrupt
      let layout ← setField layout "variants" variants
      setField original "layouts" (encodeArray (← updateAt layouts index layout))
    check (malformedResult badTagEncoding) "malformed u128 niche encoding was accepted"
  | none => fail "fixture did not exercise a structured tag encoding"

  let badRelocation ← must <| do
    let (changed, found) ← replaceFirstField original "storage_offset_bytes" (number 999999)
    if !found then throw "fixture does not contain a relocation"
    pure changed
  check (malformedResult badRelocation) "relocation bytes outside the allocation were accepted"

  let producer ← must (getField original "producer")
  let badProducer ← must (setField producer "rustc_commit" (string "not-the-pinned-rustc"))
  let badPin ← must (setField original "producer" badProducer)
  check (malformedResult badPin) "wrong rustc pin was accepted"

  let danglingType ← must <| rewriteFirstBody original fun body => do
    let locals ← array (← getField body "locals")
    let first ← getAt locals 0
    let first ← setField first "type" (number 999999)
    setField body "locals" (encodeArray (← updateAt locals 0 first))
  check (malformedResult danglingType) "dangling type reference was accepted"
  let danglingAlloc ← must <| do
    let allocations ← array (← getField original "allocations")
    let some index := document.allocations.toList.findIdx? (fun node =>
      node.memory.any fun memory => !memory.relocations.isEmpty)
      | throw "fixture contains no relocation target"
    let allocation ← getAt allocations index
    let relocations ← array (← getField allocation "relocations")
    let first ← getAt relocations 0
    let first ← setField first "target" (number 999999)
    let allocation ← setField allocation "relocations" (encodeArray (← updateAt relocations 0 first))
    setField original "allocations" (encodeArray (← updateAt allocations index allocation))
  check (malformedResult danglingAlloc) "dangling allocation reference was accepted"

  let typesJson ← must (getField original "types")
  let types ← must (array typesJson)
  let secondType ← must (getAt types 1)
  let duplicateType ← must (setField secondType "type_id" (number 0))
  let duplicateTypes ← must (updateAt types 1 duplicateType)
  let duplicateId ← must (setField original "types" (encodeArray duplicateTypes))
  check (malformedResult duplicateId) "duplicate graph-node ID was accepted"

  let allocationsJson ← must (getField original "allocations")
  let allocations ← must (array allocationsJson)
  let firstAllocation ← must (getAt allocations 0)
  let duplicateAllocations := allocations.push firstAllocation
  let duplicateAllocationId ← must (setField original "allocations" (encodeArray duplicateAllocations))
  check (malformedResult duplicateAllocationId) "duplicate allocation ID was accepted"

  let instancesJson ← must (getField original "instances")
  let instances ← must (array instancesJson)
  let secondInstance ← must (getAt instances 1)
  let duplicateInstance ← must (setField secondInstance "instance_id" (number 0))
  let duplicateInstances ← must (updateAt instances 1 duplicateInstance)
  let duplicateInstanceId ← must (setField original "instances" (encodeArray duplicateInstances))
  check (malformedResult duplicateInstanceId) "duplicate instance ID was accepted"

  let danglingInstance ← must <| do
    let roots ← array (← getField original "body_roots")
    let root ← getAt roots 0
    let root ← setField root "entry_instance" (number 999999)
    setField original "body_roots" (encodeArray (← updateAt roots 0 root))
  check (malformedResult danglingInstance) "dangling instance reference was accepted"

  let badLocal ← must <| rewriteFirstBody original fun body => do
    let locals ← array (← getField body "locals")
    let firstLocal ← getAt locals 0
    let changed ← setField firstLocal "local" (number 999999)
    setField body "locals" (encodeArray (← updateAt locals 0 changed))
  check (malformedResult badLocal) "out-of-range local declaration was accepted"

  let badLocalReference ← must <| rewriteFirstBody original fun body =>
    rewriteFirstBlock body fun block =>
      rewriteFirstTerminator block fun terminator => do
        let badPlace := object [("local",number 999999),("type",number 0),("projection","[]")]
        let badOperand := object [("kind",string "Copy"),("place",badPlace)]
        let kind := object [("variant",string "SwitchInt"),("discriminant",badOperand),("targets","[]"),("otherwise","0")]
        setField terminator "kind" kind
  check (malformedResult badLocalReference) "out-of-range local reference was accepted"

  let badEdge ← must <| rewriteFirstBody original fun body =>
    rewriteFirstBlock body fun block =>
      rewriteFirstTerminator block fun terminator => do
        let badKind := object [("variant", string "Goto"), ("target", number 999999), ("loop_hints","[]")]
        setField terminator "kind" badKind
  check (malformedResult badEdge) "out-of-range basic-block edge was accepted"

  let badProjection ← must <| rewriteFirstBody original fun body =>
    rewriteFirstBlock body fun block =>
      rewriteFirstTerminator block fun terminator => do
        let place := object [("local","0"),("type","0"),("projection",encodeArray #[object [("kind",string "Field"),("index","0")]])]
        let operand := object [("kind",string "Copy"),("place",place)]
        let kind := object [("variant",string "SwitchInt"),("discriminant",operand),("targets","[]"),("otherwise","0")]
        setField terminator "kind" kind
  check (malformedResult badProjection) "incomplete projection payload was accepted"

  let futureVariant ← must <| rewriteFirstBody original fun body =>
    rewriteFirstBlock body fun block =>
      rewriteFirstTerminator block fun terminator => do
        let future := object [("variant", string "NewPinnedVariant")]
        setField terminator "kind" future
  check (malformedResult futureVariant) "futureVariant: failed input was accepted"

  let unknownIntegerType ← must <| do
    let (changed, found) ← replaceFirstField original "signed_kind" (string "i256")
    if !found then throw "fixture does not contain a signed integer kind"
    pure changed
  check (malformedResult unknownIntegerType) "unknownIntegerType: failed input was accepted"

  let contradictoryIntegerType ← must <| do
    let (changed, found) ← replaceFirstField original "signed_kind" (string "u8")
    if !found then throw "fixture does not contain a signed integer kind"
    pure changed
  check (malformedResult contradictoryIntegerType) "contradictoryIntegerType: failed input was accepted"

  let firstRoot ← must (getAt (← must (array (← must (getField original "body_roots")))) 0)
  let rootPath ← must (getField firstRoot "def_path")
  let rootId ← must (getField firstRoot "def_id")
  let rootedScope := object [
    ("kind", string "rooted_structural_closure"),
    ("semantics", string "structural_export_closure_only"),
    ("roots", encodeArray #[object [("def_path", rootPath), ("def_id", rootId)]])]
  let scopedButIncompleteGraph ← must (setField original "selected_scope" rootedScope)
  let scopedButIncompleteGraph ← must <| do
    let types ← array (← getField scopedButIncompleteGraph "types")
    let first ← getAt types 0
    let first ← setField first "layout" (number 999999999)
    setField scopedButIncompleteGraph "types" (encodeArray (← updateAt types 0 first))
  check (malformedResult scopedButIncompleteGraph) "selected scope erased failed catalog data"

  check (!(decodeJson "{}").isOk) "missing schema and compiler tables were accepted"

  IO.println s!"input decoder tests passed: bodies={document.bodies.size}, instance_bodies={document.instances.filter (·.bodyId.isSome) |>.size}, types={document.types.size}"
  return 0
