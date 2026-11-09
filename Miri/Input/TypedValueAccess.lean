import Miri.Input.Model.Types

namespace Miri.Input.TypedValue

def fields : TypedValue → Except String (Array (String × TypedValue))
  | .object values | .enumTag _ _ values | .statement _ values | .terminator _ values
  | .rvalue _ values | .operand _ values | .projection _ values => pure values
  | _ => throw "expected typed source object"

def field (value : TypedValue) (name : String) : Except String TypedValue := do
  let some (_, child) := (← fields value).find? (·.1 == name)
    | throw s!"missing typed source field {name}"
  pure child

def elements : TypedValue → Except String (Array TypedValue)
  | .array values => pure values
  | _ => throw "expected typed source array"

def natural : TypedValue → Except String Nat
  | .scalar value => value.getNat?
  | .typeRef id | .allocationRef id | .instanceRef id | .localRef id | .blockRef id
  | .sourceSpan id => pure id
  | _ => throw "expected typed source number or reference"

def tag (value : TypedValue) : Except String String := do
  match value with
  | .enumTag _ tag _ => pure tag.tag
  | _ =>
    match ← field value "kind" with
    | .scalar name => name.getStr?
    | _ => throw "expected typed source tag"

end Miri.Input.TypedValue

namespace Miri.Input.MirNode

def envelope (node : MirNode) : TypedValue :=
  .object #[("kind", node.value), ("source_info", .sourceInfo node.sourceInfo)]

end Miri.Input.MirNode
