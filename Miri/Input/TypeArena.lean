import Miri.Input.Model.Types

/-! Execution-local lazy type identities. Material IDs occupy `[0, size)`;
constructed IDs encode a mutable raw pointer or erased mutable reference and its
pointee. The encoding is relative to this immutable input, with no global cache.
Nodes are reconstructed only when queried, so constructors can create types
absent from the export. Array IDs use a third tag and a fixed-width target-usize length payload.
Layouts are computed separately by RuntimeMetadata, never borrowed from a node
with the same representation. -/
namespace Miri.Input.TypeArena

def constructedId (materialSize : Nat) (pointee : TypeId) (isReference : Bool) : TypeId :=
  materialSize + 3 * pointee + if isReference then 1 else 0

def arrayId (materialSize : Nat) (element : TypeId) (count : UInt64) : TypeId :=
  materialSize + 3 * (element * 2^64 + count.toNat) + 2

def isDense (nodes : Array TypeNode) : Bool :=
  nodes.zipIdx.all fun (value, index) => value.id == index

def validateMaterial (nodes : Array TypeNode) : Except String Unit := do
  unless isDense nodes do throw "material type ID/index mismatch"

def nodeWithFuel (nodes : Array TypeNode) (constantBase : Nat) : Nat → TypeId → Except String TypeNode
  | 0, _ => .error "lazy type arena recursion exhausted"
  | fuel + 1, id => do
    if id < nodes.size then
      let some value := nodes[id]? | throw "material type is absent"
      unless value.id == id do throw "material type ID/index mismatch"
      return value
    unless nodes.size > 0 do throw "lazy type arena requires a material universe"
    let offset := id - nodes.size
    let payload := offset / 3
    let shape ← if offset % 3 == 2 then do
      let element := payload / 2^64
      let count := payload % 2^64
      let _ ← nodeWithFuel nodes constantBase fuel element
      pure (TypeShape.array element (constantBase + count) ⟨count, true⟩)
    else do
      let _ ← nodeWithFuel nodes constantBase fuel payload
      pure (if offset % 3 == 0 then TypeShape.rawPointer payload .Mut
        else TypeShape.reference payload .Mut .Erased)
    return { id, shape, display := "", layoutId := 0 }

def node (nodes : Array TypeNode) (id : TypeId) (constantBase : Nat := 0) : Except String TypeNode := do
  validateMaterial nodes
  nodeWithFuel nodes constantBase (id + 1) id

def intern (nodes : Array TypeNode) (pointee : TypeId) (isReference : Bool) : Except String TypeId := do
  let _ ← node nodes pointee
  let matching := nodes.filter fun value => match value.shape with
    | .rawPointer ty .Mut => !isReference && ty == pointee
    | .reference ty .Mut .Erased => isReference && ty == pointee
    | _ => false
  if let some first := matching[0]? then
    unless matching.all (·.id == first.id) do
      throw "ambiguous material type constructor identity"
    return first.id
  unless nodes.size > 0 do throw "lazy type arena requires a material universe"
  return constructedId nodes.size pointee isReference

def internArray (nodes : Array TypeNode) (element : TypeId) (count : UInt64) : Except String TypeId := do
  let _ ← node nodes element
  let matching := nodes.filter fun value => match value.shape with
    | .array ty _ constructor => ty == element && constructor.count == count.toNat &&
        constructor.canonicalValueConstructor
    | _ => false
  if let some first := matching[0]? then
    unless matching.all (·.id == first.id) do throw "ambiguous material array constructor identity"
    return first.id
  return arrayId nodes.size element count

end Miri.Input.TypeArena
