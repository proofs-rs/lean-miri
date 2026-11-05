import Miri.Input.SharedPayloads
import Miri.Input.BinaryImage
import Miri.Input.MirTags

/-! Optional structural-hash memo for already resolved transport graphs.
The authoritative resolver still owns all input checks. Cached keys use the
same Json equality and hash; collisions are never treated as equality. A raw
noncanonical object, or an unexpected shape, disables this optimization.
-/
namespace Miri.Input.JsonTraversalCache
open Lean

structure Key where
  private mk ::
  value : Json
  digest : UInt64
  /-- Existing exporter node ID. Inline nodes are not independently memoized. -/
  id : Option Nat
  /-- Conservative descendant field classes, computed from the actual graph.
  Bits: reference IDs, MIR bodies, FnAbi records, vtable casts. -/
  interests : UInt8 := 255
  /-- Conservative runtime-parser summary, computed locally for prepared rows.
  Legacy/raw nodes default to the full scan; this is not a transport hint. -/
  runtimeChecks : Bool := true

instance : BEq Key where
  beq a b := a.value == b.value
instance : Hashable Key where
  hash a := a.digest

theorem Key.beq_eq (a b : Key) : (a == b) = (a.value == b.value) := rfl

inductive Node where
  | cached (key : Key) (children : Array Node)
  | uncached (value : Json)

def Node.value : Node → Json
  | .cached key _ => key.value
  | .uncached value => value

def Node.key : Node → Key
  | .cached key _ => key
  | .uncached value => ⟨value, hash value, none, 255, true⟩

/-- Uncached JSON always takes the complete scan. A zero bit can only come
from the internal bottom-up builder, never from an unchecked producer hint. -/
def Node.mayContain (node : Node) (mask : UInt8) : Bool :=
  match node with
  | .cached key _ => key.interests &&& mask != 0
  | .uncached _ => true

/-- A summary may be used only in the generic any-domain/untagged context,
and only when the child's summary is discarded. Classification keys live here
so both transport readers compute identical summaries from the actual values. -/
private inductive RuntimeFieldClass where
  | inert | status | autoTag | context | marker (bit : UInt8)

private def runtimeFieldClass (name : String) : RuntimeFieldClass :=
  match name with
  | "status" => .status
  | "kind" | "variant" => .autoTag
  | "lo" => .marker 1 | "hi" => .marker 2
  | "start" => .marker 4 | "end" => .marker 8
  | "ctxt" => .marker 16 | "file" => .marker 32
  | "span" => .marker 64 | "scope" => .marker 128
  | "safety" | "borrow_kind" | "fake_kind" | "mutability_kind" | "mutability"
  | "cast_kind" | "coercion" | "source" | "aggregate_kind" | "unwind"
  | "phase" | "injection_phase" | "retag" | "check" | "cause" | "call_source"
  | "reason" | "region" | "bound_kind" | "index_kind" | "parameter"
  | "signed_kind" | "unsigned_kind" | "integer_kind" | "float_kind" | "adt_kind"
  | "variance" | "coverage" | "point_kind" | "retag_mode"
  | "rvalue" | "operand" | "function" | "condition" | "discriminant"
  | "projection" | "statements" | "terminator" | "operator" | "user_type_projection" => .context
  | _ => .inert

private def runtimeFieldRisk (kind : RuntimeFieldClass) (value : Json) : Bool :=
  match kind with
  | .inert | .marker _ => false
  | .context => true
  | .status => match value with
    | .str "supported" | .str "complete" | .str "debug_payload" => false
    | _ => true
  | .autoTag => match value with
    | .str tag => DecoderValues.isKnownStatement tag || DecoderValues.isKnownTerminator tag ||
        DecoderValues.isKnownRvalue tag || DecoderValues.isKnownOperand tag || DecoderValues.isKnownProjection tag
    | _ => true

private def runtimeMarker (kind : RuntimeFieldClass) : UInt8 :=
  match kind with | .marker bit => bit | _ => 0

def Node.mayHaveRuntimeChecks : Node → Bool
  | .cached key _ => key.runtimeChecks
  | .uncached _ => true

private def fieldInterest (name : String) : UInt8 :=
  if name == "type_id" || name == "allocation_id" || name == "instance_id" then 1
  else if name == "locals" || name == "basic_blocks" then 2
  else if name == "fn_abi" || name == "calling_convention" then 4
  else if name == "vtable_allocation" then 8
  else 0

/-- Dictionary-local facts are computed once, not for every field occurrence.
The source field ID only selects a checked descriptor; it supplies no hashes or
semantic hints. -/
private structure FieldInfo where
  name : String
  kind : RuntimeFieldClass
  digest : UInt64
  interests : UInt8
  marker : UInt8

private def fieldInfo (name : String) : FieldInfo :=
  let kind := runtimeFieldClass name
  ⟨name, kind, hash name, fieldInterest name, runtimeMarker kind⟩

/-- Identity keys are confined to a single document traversal. Sharing is
supplied by the exporter, never inferred from hashes. -/
inductive IdentityKey where
  | node (id : Nat)
  | raw (key : Key)
  deriving BEq

instance : Hashable IdentityKey where
  hash
    | .node id => mixHash 31 (hash id)
    | .raw key => hash key

/-- Per-traversal membership for the producer's dense node IDs. Raw JSON and
out-of-range IDs retain the ordinary exact-key set. No hash is used as identity. -/
structure IdentitySet where
  private mk ::
  private nodes : ByteArray
  private fallback : Std.HashSet IdentityKey

def IdentitySet.empty (nodeCount : Nat := 0) : IdentitySet :=
  ⟨⟨Array.replicate nodeCount 0⟩, {}⟩

def IdentitySet.contains (set : IdentitySet) (key : IdentityKey) : Bool :=
  match key with
  | .node id => if h : id < set.nodes.size then set.nodes[id]'h != 0 else set.fallback.contains key
  | .raw _ => set.fallback.contains key

def IdentitySet.insert (set : IdentitySet) (key : IdentityKey) : IdentitySet :=
  match key with
  | .node id => if h : id < set.nodes.size then { set with nodes := set.nodes.set id 1 h }
    else { set with fallback := set.fallback.insert key }
  | .raw _ => { set with fallback := set.fallback.insert key }

def Node.identity : Node → IdentityKey
  | .cached key _ => match key.id with
    | some id => .node id
    | none => .raw key
  | .uncached value => .raw ⟨value, hash value, none, 255, true⟩

/-- Inline children are traversed under their shared parent, without creating
unique memo entries that can never be hit. Raw fallback keeps structural reuse. -/
def Node.shouldMemo : Node → Bool
  | .cached key _ => key.id.isSome
  | .uncached _ => true

private def Node.withId (node : Node) (id : Nat) : Node :=
  match node with
  | .cached key children =>
    if key.id.isSome then node else .cached { key with id := some id } children
  | .uncached _ => node

theorem uncached_hash_eq (value : Json) :
    hash (Node.uncached value).key = hash value := rfl

/-- Child positions follow the actual array or object's inorder traversal.
Only the internal builder supplies cached children; an absent child falls back
to the real JSON value, preserving checks rather than treating it as visited. -/
def Node.child (node : Node) (index : Nat) (fallback : Json) : Node :=
  match node with
  | .cached _ children => (children[index]?).getD (.uncached fallback)
  | .uncached _ => .uncached fallback

def Node.field (node : Node) (name : String) (fallback : Json) : Node := Id.run do
  let .obj fields := node.value | return .uncached fallback
  for ((key,_),index) in fields.toList.zipIdx do
    if key == name then return node.child index fallback
  return .uncached fallback

private partial def canonicalRaw : Json → Bool
  | .obj fields => Id.run do
      let mut previous : Option String := none
      for (key,value) in fields.toList do
        if let some old := previous then
          unless old < key do return false
        if !canonicalRaw value then return false
        previous := some key
      return true
  | .arr values => values.all canonicalRaw
  | _ => true

/-- Pair raw transport children with the authoritative resolver's actual JSON.
Reference edges reuse the earlier node, so computing the parent hash does not
recursively hash a resolved shared subtree. No JSON is normalized/replaced. -/
private partial def buildNode (available : Array Node) (raw actual : Json) : Option Node := do
  if let .obj fields := raw then
    if fields.contains "$lean_miri_shared_ref" then
      let id ← ((raw.getObjVal? "$lean_miri_shared_ref").bind Json.getNat?).toOption
      return ← available[id]?
  match raw, actual with
  | .arr source, .arr values =>
      if source.size != values.size then none else do
        let mut children := #[]
        let mut digest : UInt64 := 7
        let mut interests : UInt8 := 0
        for index in [:values.size] do
          let child ← buildNode available (← source[index]?) (← values[index]?)
          digest := mixHash digest child.key.digest
          interests := interests ||| child.key.interests
          children := children.push child
        return .cached ⟨actual, mixHash 23 digest, none, interests, true⟩ children
  | .obj source, .obj fields =>
      let source := source.toList.toArray
      let entries := fields.toList.toArray
      if source.size != entries.size then none else do
        let mut children := #[]
        let mut digest : UInt64 := 7
        let mut interests : UInt8 := 0
        for index in [:entries.size] do
          let (name,value) ← entries[index]?
          let (sourceName,sourceValue) ← source[index]?
          if name != sourceName then return ← none
          let child ← buildNode available sourceValue value
          digest := mixHash digest (mixHash (hash name) child.key.digest)
          interests := interests ||| fieldInterest name ||| child.key.interests
          children := children.push child
        return .cached ⟨actual, mixHash 29 digest, none, interests, true⟩ children
  | .arr _, _ | .obj _, _ => none
  | _, _ => return .cached ⟨actual, hash actual, none, 0, true⟩ #[]

private def buildRoot (input : Json) (resolved : SharedPayloads.ResolvedGraph) : Option (Node × ByteArray) := do
  if !canonicalRaw input then return ← none
  let rawNodes ← (((input.getObjVal? "shared_payloads").bind fun j => j.getObjVal? "nodes").bind Json.getArr?).toOption
  if rawNodes.size != resolved.nodes.size then return ← none
  let mut available := #[]
  let mut flags := ByteArray.empty
  for index in [:rawNodes.size] do
    let node ← buildNode available (← rawNodes[index]?) (← resolved.nodes[index]?)
    available := available.push (node.withId index)
    flags := flags.push node.key.interests
  let .obj fields := input | return ← none
  let business := Json.mkObj (fields.toList.filter (fun entry => entry.1 != "shared_payloads"))
  return (← buildNode available business resolved.root, flags)

private def scalarNode (index : Nat) (value : Json) : Node :=
  .cached ⟨value, hash value, some index, 0, false⟩ #[]

private def arrayNode (index : Nat) (children : Array Node) : Node := Id.run do
  let mut digest : UInt64 := 7
  let mut interests : UInt8 := 0
  let mut runtimeChecks := false
  let mut values := #[]
  for child in children do
    values := values.push child.value
    digest := mixHash digest child.key.digest
    interests := interests ||| child.key.interests
    runtimeChecks := runtimeChecks || child.mayHaveRuntimeChecks
  return .cached ⟨.arr values, mixHash 23 digest, some index, interests, runtimeChecks⟩ children

private def objectNode (index : Nat) (entries : Array (FieldInfo × Node)) : Node := Id.run do
  let mut digest : UInt64 := 7
  let mut interests : UInt8 := 0
  let mut runtimeChecks := false
  let mut values := #[]
  let mut children := #[]
  let mut markers : UInt8 := 0
  let mut diagnostic := false
  for (info, child) in entries do
    let name := info.name
    runtimeChecks := runtimeChecks || runtimeFieldRisk info.kind child.value
    markers := markers ||| info.marker
    if let .status := info.kind then
      if child.value == .str "debug_payload" then diagnostic := true
    values := values.push (name, child.value)
    children := children.push child
    digest := mixHash digest (mixHash info.digest child.key.digest)
    interests := interests ||| info.interests ||| child.key.interests
    runtimeChecks := runtimeChecks || child.mayHaveRuntimeChecks
  runtimeChecks := !diagnostic && (runtimeChecks || markers &&& 63 == 63 || markers &&& 192 == 192)
  return .cached ⟨.obj (Std.TreeMap.Raw.ofArray values), mixHash 29 digest, some index, interests, runtimeChecks⟩ children

private def finishPreparedGraph (available : Array Node) (values : Array Json) (root : Nat) :
    Except String (SharedPayloads.ResolvedGraph × Node) := do
  let some node := available[root]? | throw "prepared image: root ID out of range"
  let .obj fields := node.value | throw "prepared image: business root must be object"
  if fields.contains "shared_payloads" then throw "prepared image: reserved catalog field"
  pure (⟨values, node.value, values.size, none⟩, node)

/-- Decode the versioned execution graph directly into its indexed runtime
nodes. All edges, field names and row shapes are checked before use. Digests
and traversal summaries are computed locally, never trusted from the producer. -/
private def preparedGraph (input : Json) : Except String (SharedPayloads.ResolvedGraph × Node) := do
  let .obj header := input | throw "prepared image: expected object"
  let names := header.toList.map Prod.fst
  unless names == ["fields", "nodes", "root", "schema", "schema_version"] do
    throw "prepared image: unexpected or missing header fields"
  unless (← input.getObjValAs? Nat "schema_version") == 1 do
    throw "prepared image: unsupported schema version"
  let fields ← (← input.getObjVal? "fields").getArr?
  let mut dictionary : Array FieldInfo := #[]
  let mut seen : Std.HashSet String := {}
  for field in fields do
    let name ← field.getStr?
    if seen.contains name then throw "prepared image: duplicate field name"
    seen := seen.insert name
    dictionary := dictionary.push (fieldInfo name)
  let rows ← (← input.getObjVal? "nodes").getArr?
  let mut available : Array Node := #[]
  let mut values : Array Json := #[]
  for h : index in [:rows.size] do
    let row ← rows[index].getArr?
    let item := fun (i : Nat) => match row[i]? with
      | some value => Except.ok value
      | none => Except.error "prepared image: missing row payload"
    let some tagJson := row[0]? | throw "prepared image: empty node row"
    let tag ← tagJson.getNat?
    let child := fun (id : Json) => do
      let id ← id.getNat?
      let some node := available[id]? | throw s!"prepared image: node {index} has forward/out-of-range edge {id}"
      pure node
    let node ← match tag with
      | 0 | 1 | 2 => do
        unless row.size == 1 do throw "prepared image: scalar row arity"
        pure (scalarNode index (if tag == 0 then Json.null else Json.bool (tag == 2)))
      | 3 | 4 => do
        unless row.size == 2 do throw "prepared image: leaf row arity"
        let value := (← item 1)
        match tag, value with
        | 3, .num _ | 4, .str _ => pure ()
        | _, _ => throw "prepared image: leaf payload type"
        pure (scalarNode index value)
      | 5 => do
        unless row.size == 2 do throw "prepared image: array row arity"
        let ids ← (← item 1).getArr?
        let mut children := #[]
        for id in ids do children := children.push (← child id)
        pure (arrayNode index children)
      | 6 => do
        unless row.size == 2 do throw "prepared image: object row arity"
        let pairs ← (← item 1).getArr?
        let mut entries := #[]
        let mut previous : Option String := none
        for pair in pairs do
          let pair ← pair.getArr?
          unless pair.size == 2 do throw "prepared image: field row arity"
          let some fieldId := pair[0]? | throw "prepared image: missing field ID"
          let id ← fieldId.getNat?
          let some info := dictionary[id]? | throw "prepared image: field ID out of range"
          let name := info.name
          if let some old := previous then
            unless old < name do throw "prepared image: object fields are not strictly ordered"
          if name == "$lean_miri_shared_ref" then throw "prepared image: reserved reference field"
          let some childId := pair[1]? | throw "prepared image: missing field edge"
          let node ← child childId
          previous := some name
          entries := entries.push (info, node)
        pure (objectNode index entries)
      | _ => throw "prepared image: unknown node kind"
    available := available.push node
    values := values.push node.value
  finishPreparedGraph available values (← input.getObjValAs? Nat "root")

private def binaryGraphM : BinaryImage.Reader (SharedPayloads.ResolvedGraph × Node) := do
  let count ← BinaryImage.readCount
  let mut dictionary : Array FieldInfo := #[]
  let mut seen : Std.HashSet String := {}
  for _ in [:count] do
    let name ← BinaryImage.readText
    if seen.contains name then throw "prepared image: duplicate field name"
    seen := seen.insert name
    dictionary := dictionary.push (fieldInfo name)
  let count ← BinaryImage.readCount
  let mut available : Array Node := #[]
  let mut values : Array Json := #[]
  for index in [:count] do
    let child : BinaryImage.Reader Node := do
      let id ← BinaryImage.readNat
      let some node := available[id]? | throw s!"prepared image: node {index} has forward/out-of-range edge {id}"
      return node
    let tag ← BinaryImage.readByte
    let node ← match tag.toNat with
      | 0 | 1 | 2 => pure (scalarNode index (if tag == 0 then .null else .bool (tag == 2)))
      | 3 => do
        let text ← BinaryImage.readText
        let value ← match Json.parse text with
          | .ok (.num number) => pure (Json.num number)
          | _ => throw "binary image: invalid number leaf"
        pure (scalarNode index value)
      | 4 => pure (scalarNode index (.str (← BinaryImage.readText)))
      | 7 => pure (scalarNode index (.num (JsonNumber.fromNat (← BinaryImage.readNat))))
      | 8 => do
        let magnitude ← BinaryImage.readNat
        unless magnitude > 0 && magnitude ≤ 2^63 do throw "binary image: invalid negative integer"
        pure (scalarNode index (.num (JsonNumber.fromInt (-Int.ofNat magnitude))))
      | 5 => do
        let count ← BinaryImage.readCount
        let mut children := #[]
        for _ in [:count] do children := children.push (← child)
        pure (arrayNode index children)
      | 6 => do
        let count ← BinaryImage.readCount
        let mut entries := #[]
        let mut previous : Option String := none
        for _ in [:count] do
          let id ← BinaryImage.readNat
          let some info := dictionary[id]? | throw "prepared image: field ID out of range"
          let name := info.name
          if let some old := previous then
            unless old < name do throw "prepared image: object fields are not strictly ordered"
          if name == "$lean_miri_shared_ref" then throw "prepared image: reserved reference field"
          let node ← child
          previous := some name
          entries := entries.push (info, node)
        pure (objectNode index entries)
      | _ => throw "prepared image: unknown node kind"
    available := available.push node
    values := values.push node.value
  let root ← BinaryImage.readNat
  let cursor ← get
  unless cursor.position == cursor.bytes.size do throw "binary image: trailing bytes"
  match finishPreparedGraph available values root with
  | .ok result => pure result
  | .error error => throw error

/-- Direct binary transport checks every dictionary item, row and edge before
any semantic consumer runs, including unused rows. No producer digest or
readiness assertion is accepted. -/
def resolveBinary (bytes : ByteArray) : Except String (SharedPayloads.ResolvedGraph × Node) :=
  if !BinaryImage.hasMagic bytes then .error "binary image: invalid magic/version" else
  match binaryGraphM.run ⟨bytes, BinaryImage.magic.size⟩ with
  | .ok result _ => .ok result
  | .error error _ => .error error

/-- Only this constructor path creates the optional cache from the same input
and resolver result. Fallback preserves arbitrary manually constructed Raw JSON.
The cache performs no readiness or semantic validation of its own. -/
def resolve (input : Json) (enabled : Bool := true) (profile : Options := {}) :
    Except String (SharedPayloads.ResolvedGraph × Node) := do
  if (input.getObjValAs? String "schema").toOption == some "lean-miri-prepared-image" then
    let (resolved,node) ← profileit "decoder.prepared_graph" profile fun _ => preparedGraph input
    return (resolved, if enabled then node else .uncached resolved.root)
  let resolved ← SharedPayloads.resolveGraph input
  let built := if enabled || resolved.scanFlags.isSome then
    profileit "decoder.traversal_hash_cache" profile (fun _ => buildRoot input resolved)
    else none
  if let some supplied := resolved.scanFlags then
    let some (_, computed) := built
      | throw "$.shared_payloads.scan_flags: cannot validate summaries for noncanonical graph"
    unless supplied.data == computed.data do
      throw "$.shared_payloads.scan_flags: summary differs from actual graph"
  let node := if enabled then built.map Prod.fst |>.getD (.uncached resolved.root)
    else .uncached resolved.root
  return (resolved,node)

/-- Capability for a traversal produced by this module's checked resolver.
The witness prevents record updates from substituting arbitrary child nodes. -/
structure CheckedRoot where
  private mk ::
  node : Node
  private checked : (∃ (input : Json) (enabled : Bool) (profile : Options)
    (resolved : SharedPayloads.ResolvedGraph), resolve input enabled profile = .ok (resolved, node)) ∨
    (∃ (bytes : ByteArray) (resolved : SharedPayloads.ResolvedGraph),
      resolveBinary bytes = .ok (resolved, node))

def resolveChecked (input : Json) (enabled : Bool := true) (profile : Options := {}) :
    Except String (SharedPayloads.ResolvedGraph × CheckedRoot) :=
  match h : resolve input enabled profile with
  | .error error => .error error
  | .ok (resolved, node) => .ok (resolved, ⟨node, .inl ⟨input, enabled, profile, resolved, h⟩⟩)

def resolveBinaryChecked (bytes : ByteArray) :
    Except String (SharedPayloads.ResolvedGraph × CheckedRoot) :=
  match h : resolveBinary bytes with
  | .error error => .error error
  | .ok (resolved, node) => .ok (resolved, ⟨node, .inr ⟨bytes, resolved, h⟩⟩)

/-- Diagnostic consistency check; deliberately expensive, never used as a
readiness shortcut. It checks every cached child independently. -/
partial def Node.audit (node : Node) : Bool :=
  match node with
  | .uncached _ => true
  | .cached key children =>
    let values := match key.value with
      | .arr values => values
      | .obj fields => fields.toList.toArray.map Prod.snd
      | _ => #[]
    let own := match key.value with
      | .obj fields => fields.toList.foldl (fun bits (name, _) => bits ||| fieldInterest name) 0
      | _ => 0
    let interests := children.foldl (fun bits child => bits ||| child.key.interests) own
    let runtimeChecks := match key.value with
      | .obj fields => Id.run do
        let mut checks := false
        let mut markers : UInt8 := 0
        for (name, value) in fields.toList do
          let kind := runtimeFieldClass name
          checks := checks || runtimeFieldRisk kind value
          markers := markers ||| runtimeMarker kind
        let diagnostic := (key.value.getObjValAs? String "status").toOption == some "debug_payload"
        return !diagnostic && (checks || markers &&& 63 == 63 || markers &&& 192 == 192 ||
          children.any Node.mayHaveRuntimeChecks)
      | .arr _ => children.any Node.mayHaveRuntimeChecks
      | _ => false
    (key.runtimeChecks || !runtimeChecks) && key.interests == interests && key.digest == hash key.value && values.size == children.size &&
      (values.zip children).all (fun (value,child) => value == child.value) &&
      children.all Node.audit

end Miri.Input.JsonTraversalCache
