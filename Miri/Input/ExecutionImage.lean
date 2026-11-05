import Lean

/-! Native producer boundary. These are typed source graph rows, not trusted
execution evidence. JsonTraversalCache validates every row, edge and dictionary
entry before the ordinary semantic importer can compile an execution IR. -/
namespace Miri.Input.ExecutionImage
open Lean

inductive Row where
  | null
  | boolean (value : Bool)
  | number (value : JsonNumber)
  | string (value : String)
  | array (children : Array Nat)
  | object (fields : Array (Nat × Nat))

structure Image where
  fields : Array String
  nodes : Array Row
  root : Nat

-- C ABI factories use safe Lean constructors. No untyped object deserialization,
-- memory image, fabricated proof or cached readiness bit crosses the boundary.
@[export lean_miri_ir_scalar]
def scalar (tag : UInt8) (text : String) : Except String Row := do
  match tag.toNat with
  | 0 => pure .null
  | 1 => pure (.boolean false)
  | 2 => pure (.boolean true)
  | 3 =>
    let .num value ← Json.parse text | throw "execution image: invalid number"
    pure (.number value)
  | 4 => pure (.string text)
  | _ => throw "execution image: invalid scalar tag"

@[export lean_miri_ir_array]
def array (children : Array Nat) : Row := .array children
@[export lean_miri_ir_object]
def object (fields : Array (Nat × Nat)) : Row := .object fields
@[export lean_miri_ir_image]
def image (fields : Array String) (nodes : Array Row) (root : Nat) : Image :=
  ⟨fields, nodes, root⟩
end Miri.Input.ExecutionImage
