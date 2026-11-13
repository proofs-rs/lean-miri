import Miri

/-! Run with the canonical source3 full document. This is an error-transport
regression using deliberately failing capabilities, not a CTFE value oracle.
The physical source IDs are checked before traversal; no normalized scalar
answer is supplied. Genuine evaluation and allocation are tested separately. -/
open Lean Miri.Input Miri.Interpreter
private def must [ToString ε] (value : Except ε α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private structure State where
  types : RuntimeArrayTypes.World
  reached : Nat := 0
private def arrays : RuntimeArrayQueries.Access State := ⟨(·.types),fun s types => {s with types}⟩
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [path,oraclePath] := args | throw (IO.userError "expected canonical source3 document and independent SizedPointerOracle JSON")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let expectedSize ← must ((← must (oracle.getObjVal? "pointer_size")).getNat?)
  let expectedAlign ← must ((← must (oracle.getObjVal? "pointer_align")).getNat?)
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let some source := document.types[939]? | throw (IO.userError "source inner absent")
  let .adt adt := source.shape | throw (IO.userError "expected raw NonZeroU64Inner")
  let some owner := document.definitions[adt.definition]? | throw (IO.userError "owner absent")
  check (owner.crateIndex == 2 && owner.index == 36655) "physical source inner changed"
  let provider : RuntimeEffectfulLayout.Provider State := fun _ _ _ _ => do
    modify fun state => {state with reached := state.reached + 1}
    throw (.invalidProgram "sized pointer must not demand a constant")
  let action : RvalueM State LocalLayout := do
    let pointer ← RuntimeArrayQueries.perform arrays (TypeArena.World.internType (.rawPointer 939 .Not))
    RuntimeEffectfulLayout.layout arrays provider CompilerTypingEnv.fullyMonomorphized none runtime pointer
  match action.run {types := initial} with
  | .error error _ => throw (IO.userError s!"sized pointer failed: {reprStr error}")
  | .ok result next =>
    check (result.layout.size.bytes.toNat == expectedSize) "sized pointer width differs from independent Rust"
    let actualAlign ← must (result.layout.align.abi.bytes)
    check (actualAlign.toNat == expectedAlign) "sized pointer alignment differs from independent Rust"
    check (next.reached == 0) "sized pointer eagerly demanded Pattern constant"
  let metadataAction : RvalueM State TypeId := do
    -- Build a raw Pattern with the actual physical alias still unevaluated.
    -- This is a constructor/query-order control, not a scalar CTFE answer.
    let raw ← RuntimeArrayQueries.perform arrays do
      let arena ← get
      let definition ← match arena.definitionRef ⟨2,69102⟩ with
        | .ok value => pure value
        | .error error => throw error
      let base ← TypeArena.World.internType (.integer false .u64)
      let lower ← TypeArena.World.internConstant (.Value base ⟨#[.Leaf 1 8],0⟩)
      let upper ← TypeArena.World.internConstant (.Alias false .Anon definition #[])
      TypeArena.World.internType (.patternType base (.range lower upper))
    RuntimeEffectfulLayout.pointerMetadataType arrays provider CompilerTypingEnv.fullyMonomorphized none runtime raw
  match metadataAction.run {types := initial} with
  | .error error _ => throw (IO.userError s!"raw Pattern metadata failed: {reprStr error}")
  | .ok metadata next =>
    check (metadata == runtime.source.queries.primitives.unit) "raw Pattern metadata is not unit"
    check (next.reached == 0) "struct_tail_raw normalized Pattern self/bound eagerly"
  let bad : RvalueM State TypeId := RuntimeEffectfulLayout.fieldType arrays provider
    CompilerTypingEnv.fullyMonomorphized none runtime 939 0 1
  match bad.run {types := initial} with
  | .ok _ _ => throw (IO.userError "nonexistent source field succeeded")
  | .error _ next => check (next.reached == 0) "bounds failure evaluated a field constant"
  IO.println "source pointer/field order PASS: sized pointer skips CTFE; invalid field rejected before provider (no fake CTFE success)"
