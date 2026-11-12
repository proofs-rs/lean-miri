import Miri.Input.Model

namespace Miri.Input.StructuralNormalization

/-- Pinned rustc `try_normalize_erasing_regions` returns the erased input when
`has_aliases` is false (ty/normalize_erasing_regions.rs:119–129). This recognizer
covers primitive types, tuples, slices and pointers/references whose complete
children are already region erased. Other forms require residual normalization
material; false is not a claim that normalization fails or changes the type.
Fuel exhaustion and absent nodes are errors, never identity normalization. -/
def identityReady (nodes : Array TypeNode) : Nat → TypeId → Except String Bool
  | 0, _ => .error "structural normalization traversal exhausted"
  | fuel + 1, id => do
    let some node := nodes.find? (·.id == id)
      | throw "structural normalization type is absent"
    match node.shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never | .foreign _ => pure true
    | .slice child | .rawPointer child _ => identityReady nodes fuel child
    | .reference child _ .Erased => identityReady nodes fuel child
    | .tuple children => do
      let mut ready := true
      for child in children do
        ready := (← identityReady nodes fuel child) && ready
      pure ready
    | _ => pure false

end Miri.Input.StructuralNormalization
