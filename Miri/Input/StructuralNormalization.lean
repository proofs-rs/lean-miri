import Miri.Input.Model
import Miri.Input.TypeArena

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

/-- Shared normalization dependency for structural compiler queries. Lazy
constructors normalize children and re-intern exact identities; complex material
forms still require an explicitly marked residual compiler normalization result.
This function does not claim to solve alias/trait normalization. -/
def normalize (lookup : TypeId → Except String TypeNode) (nodes : Array TypeNode) :
    Nat → TypeId → Except String TypeId
  | 0, _ => .error "lazy normalization traversal exhausted"
  | fuel + 1, id => do
    let source ← lookup id
    if id >= nodes.size then
      match source.shape with
      | .rawPointer child .Mut =>
        TypeArena.intern nodes (← normalize lookup nodes fuel child) false
      | .reference child .Mut .Erased =>
        TypeArena.intern nodes (← normalize lookup nodes fuel child) true
      | .array child _ constructor =>
        TypeArena.internArray nodes (← normalize lookup nodes fuel child)
          (UInt64.ofNat constructor.count)
      | _ => throw "unknown lazy normalization constructor"
    else if ← identityReady nodes (nodes.size + 1) id then pure id
    else
      let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
      unless facts.typingEnvironment == "fully_monomorphized" do
        throw "compiler query typing-environment mismatch"
      let some (_, some target) := facts.typeQueries.find? (·.1 == "normalized")
        | throw "missing residual compiler normalization material"
      let _ ← lookup target
      pure target

end Miri.Input.StructuralNormalization
