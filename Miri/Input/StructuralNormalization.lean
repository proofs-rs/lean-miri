import Miri.Input.Model
import Miri.Input.TypeArena
import Miri.Input.AliasRuntime

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

/-- Source-only normalization dependency for focused material queries.
Execution-owned types use WorldNormalization and its stateful interner.
Complex material forms retain an explicitly marked residual normalization result.
Nonrigid free/projection aliases use the raw declaration/trait engine;
other complex forms retain the explicitly marked residual compiler result. -/
def normalize (lookup : TypeId → Except String TypeNode) (document : ImportDocument) :
    Nat → TypeId → Except String TypeId
  | 0, _ => .error "material normalization traversal exhausted"
  | fuel + 1, id => do
    let source ← lookup id
    let nodes := document.types
    -- Compiler-fact queries use the exporter's explicit instantiated view for
    -- signature-bound nodes. Raw generic substitution keeps its source Binder.
    if let some queryView := source.layoutQueryInputTypeId then
      if queryView != id then return ← normalize lookup document fuel queryView
    match source.shape with
    | .alias .free false _ _ | .alias .projection false _ _ =>
      -- Nonrigid declaration aliases use the actual source-rule engine.
      -- Unsupported projection providers fail explicitly; they never read the
      -- residual normalized-answer catalog after selection/fulfillment fails.
      let context ← AliasRuntime.Context.ofDocument document
      return ← AliasRuntime.normalizeType context (min (fuel + 1) 256) 10000 id
    | _ => pure ()
    if ← identityReady nodes (nodes.size + 1) id then pure id
    else
      let some facts := source.compilerFacts | throw s!"missing compiler_facts for type {id}"
      unless facts.typingEnvironment == "fully_monomorphized" do
        throw "compiler query typing-environment mismatch"
      let some (_, some target) := facts.typeQueries.find? (·.1 == "normalized")
        | throw "missing residual compiler normalization material"
      let _ ← lookup target
      pure target

end Miri.Input.StructuralNormalization
