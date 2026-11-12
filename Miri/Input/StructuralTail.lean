import Miri.Input.Model.Types

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`compiler/rustc_middle/src/ty/util.rs::struct_tail_raw`.
ADT fields are instantiated material in TypeShape; the supplied normalization
operation is still a compiler dependency. Tuple and pattern steps do not normalize.
Fuel exhaustion is an error, never an answer. -/
namespace Miri.Input.StructuralTail

def tail (lookup : TypeId → Except String TypeShape)
    (normalize : TypeId → Except String TypeId) : Nat → TypeId → Except String TypeId
  | 0, _ => .error "structural type tail recursion exhausted"
  | fuel + 1, id => do
    match ← lookup id with
    | .adt data =>
      if data.kind != .structKind then return id
      unless data.variants.size == 1 do throw "struct type requires one material variant"
      let some variant := data.variants[0]?
        | throw "struct type lacks its material variant"
      let some field := variant.fields.back? | return id
      tail lookup normalize fuel (← normalize field.typeId)
    | .tuple elements =>
      let some last := elements.back? | return id
      tail lookup normalize fuel last
    | .patternType base _ => tail lookup normalize fuel base
    | _ => return id

end Miri.Input.StructuralTail
