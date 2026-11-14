import Miri.Input.Model.Types

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`compiler/rustc_middle/src/ty/util.rs`::is_trivially_freeze and
is_trivially_unpin. These predicates have identical rules on the input type
language. `false` means unknown, never a negative trait-solver result. Error and
fuel exhaustion remain errors. References do not recurse into their pointees. -/
namespace Miri.Input.StructuralAutoTraits

def trivial (shape : TypeId → Except String TypeShape) : Nat → TypeId → Except String Bool
  | 0, _ => .error "structural auto-trait recursion exhausted"
  | fuel + 1, ty => do
    match ← shape ty with
    | .int _ | .uint _ | .float _ | .bool | .char | .str | .never
    | .reference .. | .rawPointer .. | .functionDefinition .. | .functionPointer .. =>
      pure true
    | .tuple fields => do
      for field in fields do
        unless ← trivial shape fuel field do return false
      pure true
    | .patternType inner _ | .slice inner | .array inner .. => trivial shape fuel inner
    | _ => pure false

end Miri.Input.StructuralAutoTraits
