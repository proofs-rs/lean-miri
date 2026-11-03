import Miri.Input.SharedPayloads

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
  | .uncached value => ⟨value, hash value, none, 255⟩

/-- Uncached JSON always takes the complete scan. A zero bit can only come
from the internal bottom-up builder, never from an unchecked producer hint. -/
def Node.mayContain (node : Node) (mask : UInt8) : Bool :=
  match node with
  | .cached key _ => key.interests &&& mask != 0
  | .uncached _ => true

private def fieldInterest (name : String) : UInt8 :=
  if name == "type_id" || name == "allocation_id" || name == "instance_id" then 1
  else if name == "locals" || name == "basic_blocks" then 2
  else if name == "fn_abi" || name == "calling_convention" then 4
  else if name == "vtable_allocation" then 8
  else 0

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
  | .uncached value => .raw ⟨value, hash value, none, 255⟩

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
        return .cached ⟨actual, mixHash 23 digest, none, interests⟩ children
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
        return .cached ⟨actual, mixHash 29 digest, none, interests⟩ children
  | .arr _, _ | .obj _, _ => none
  | _, _ => return .cached ⟨actual, hash actual, none, 0⟩ #[]

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

/-- Only this constructor path creates the optional cache from the same input
and resolver result. Fallback preserves arbitrary manually constructed Raw JSON.
The cache performs no readiness or semantic validation of its own. -/
def resolve (input : Json) (enabled : Bool := true) (profile : Options := {}) :
    Except String (SharedPayloads.ResolvedGraph × Node) := do
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
    key.interests == interests && key.digest == hash key.value && values.size == children.size &&
      (values.zip children).all (fun (value,child) => value == child.value) &&
      children.all Node.audit

end Miri.Input.JsonTraversalCache
