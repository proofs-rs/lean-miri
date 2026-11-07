import Miri.Input.Reader.Catalog

/-! Traversal views for the checked transport catalog. Production uses `indexed`
nodes, inspecting one existing catalog ID at each edge without copying JSON.
Expanded transport comparison helpers live exclusively under MiriTests.
-/
namespace Miri.Input.JsonTraversalCache
open Lean

structure Key where
  private mk ::
  value : Json
  digest : UInt64
  /-- Existing exporter node ID. Inline nodes are not independently memoized. -/
  id : Option Nat

instance : BEq Key where
  beq a b := a.value == b.value
instance : Hashable Key where
  hash a := a.digest

theorem Key.beq_eq (a b : Key) : (a == b) = (a.value == b.value) := rfl

inductive Node where
  | cached (key : Key) (children : Array Node)
  | uncached (value : Json)
  | indexed (catalog : Reader.Catalog) (raw : Json)

def Node.value : Node → Json
  | .cached key _ => key.value
  | .uncached value => value
  | .indexed catalog raw => (catalog.inspect raw "traversal").toOption.getD raw

def Node.key : Node → Key
  | .cached key _ => key
  | .uncached value => ⟨value, hash value, none⟩
  | .indexed catalog raw =>
    ⟨raw, hash raw, ((catalog.sharedId? raw "traversal").toOption).getD none⟩

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

def Node.identity : Node → IdentityKey
  | .cached key _ => match key.id with
    | some id => .node id
    | none => .raw key
  | .uncached value => .raw ⟨value, hash value, none⟩
  | .indexed catalog raw =>
    match ((catalog.sharedId? raw "traversal").toOption).getD none with
    | some id => .node id
    | none => .raw ⟨raw, hash raw, none⟩

/-- Inline children are traversed under their shared parent, without creating
unique memo entries that can never be hit. Raw fallback keeps structural reuse. -/
def Node.shouldMemo : Node → Bool
  | .cached key _ => key.id.isSome
  | .uncached _ => true
  | .indexed catalog raw => (((catalog.sharedId? raw "traversal").toOption).getD none).isSome

theorem uncached_hash_eq (value : Json) :
    hash (Node.uncached value).key = hash value := rfl

/-- Child positions follow the actual array or object's inorder traversal.
Only the internal builder supplies cached children; an absent child falls back
to the real JSON value, preserving checks rather than treating it as visited. -/
def Node.child (node : Node) (index : Nat) (fallback : Json) : Node :=
  match node with
  | .cached _ children => (children[index]?).getD (.uncached fallback)
  | .uncached _ => .uncached fallback
  | .indexed catalog _ => .indexed catalog fallback

def Node.field (node : Node) (name : String) (fallback : Json) : Node := Id.run do
  let .obj fields := node.value | return .uncached fallback
  for ((key,_),index) in fields.toList.zipIdx do
    if key == name then return node.child index fallback
  return .uncached fallback

/-- Diagnostic consistency check; deliberately expensive, never used as a
readiness shortcut. It checks every cached child independently. -/
partial def Node.audit (node : Node) : Bool :=
  match node with
  | .uncached _ => true
  | .indexed catalog raw => (catalog.inspect raw "traversal").isOk
  | .cached key children =>
    let values := match key.value with
      | .arr values => values
      | .obj fields => fields.toList.toArray.map Prod.snd
      | _ => #[]
    key.digest == hash key.value && values.size == children.size &&
      (values.zip children).all (fun (value,child) => value == child.value) &&
      children.all Node.audit

/-- A lazy transport traversal. Field access observes the checked catalog node;
the original shared references remain in all child positions. -/
def fromCatalog (catalog : Reader.Catalog) : Node := .indexed catalog catalog.root

end Miri.Input.JsonTraversalCache
