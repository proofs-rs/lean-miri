import Miri.Input.Model.Types

/-! Checked access to the immutable source type prefix. Runtime constructors
live exclusively in the execution-owned TypeArena.World; numbers outside this
prefix never denote implicit or algebraically encoded types. -/
namespace Miri.Input.TypeArena

def isDense (nodes : Array TypeNode) : Bool :=
  nodes.zipIdx.all fun (value,index) => value.id == index

def validateMaterial (nodes : Array TypeNode) : Except String Unit := do
  unless isDense nodes do throw "material type ID/index mismatch"

def materialNode (nodes : Array TypeNode) (id : TypeId) : Except String TypeNode := do
  let some value := nodes[id]? | throw "material type is absent"
  unless value.id == id do throw "material type ID/index mismatch"
  pure value

def node (nodes : Array TypeNode) (id : TypeId) : Except String TypeNode := do
  validateMaterial nodes
  materialNode nodes id

def findPointer (nodes : Array TypeNode) (pointee : TypeId) (isReference : Bool) : Except String TypeId := do
  let _ ← node nodes pointee
  let matching := nodes.filter fun value => match value.shape with
    | .rawPointer ty .Mut => !isReference && ty == pointee
    | .reference ty .Mut .Erased => isReference && ty == pointee
    | _ => false
  let some first := matching[0]? | throw "pointer constructor is absent from source material"
  unless matching.all (·.id == first.id) do throw "ambiguous material type constructor identity"
  pure first.id

def findArray (nodes : Array TypeNode) (element : TypeId) (count : UInt64) : Except String TypeId := do
  let _ ← node nodes element
  let matching := nodes.filter fun value => match value.shape with
    | .array ty _ constructor => ty == element && constructor.count == count.toNat &&
        constructor.canonicalValueConstructor
    | _ => false
  let some first := matching[0]? | throw "array constructor is absent from source material"
  unless matching.all (·.id == first.id) do throw "ambiguous material array constructor identity"
  pure first.id
end Miri.Input.TypeArena
