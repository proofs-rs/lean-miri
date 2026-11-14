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
  let [path] := args | throw (IO.userError "expected canonical source3 full document")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let some source := document.types[939]? | throw (IO.userError "source inner absent")
  let .adt adt := source.shape | throw (IO.userError "expected raw NonZeroU64Inner")
  let some owner := document.definitions[adt.definition]? | throw (IO.userError "owner absent")
  check (owner.crateIndex == 2 && owner.index == 36655) "physical source inner changed"
  let empty ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] runtime.target.pointerSize.bytes.toNat)
  let instances ← must (InstanceArena.Store.ofSource empty #[])
  let novel := {initial with arena := empty,instances,bodies := BodyArena.Store.ofSource #[]}
  for isConstructed in #[false,true] do
    let (ownerType,current) ← if isConstructed then
      must ((RuntimeArrayTypes.perform novel (TypeArena.World.internType (.adt ⟨2,36655⟩ #[]))).mapError reprStr)
      else pure (939,initial)
    for unsupported in #[false,true] do
      let provider : RuntimeEffectfulLayout.Provider State := fun _ _ _ term => do
        let .definition .constant "alias_anonymous_not_rigid" definition .nil := term
          | throw (.invalidProgram "wrong demand shape")
        unless definition == ⟨2,69102⟩ do throw (.invalidProgram "wrong physical type constant")
        modify fun state => {state with reached := state.reached + 1}
        -- Deliberate failing capability: this tests passthrough and successor
        -- preservation, never supplies a candidate scalar or compiler answer.
        if unsupported then throw (.unsupported "provider sentinel")
        else throw (.invalidProgram "provider sentinel")
      let action := RuntimeEffectfulLayout.fieldType arrays provider CompilerTypingEnv.fullyMonomorphized none runtime ownerType 0 0
      match action.run {types := current} with
      | .ok _ _ => throw (IO.userError "failing provider yielded a layout")
      | .error error next =>
        let expected := if unsupported then StepError.unsupported "provider sentinel" else StepError.invalidProgram "provider sentinel"
        check (reprStr error == reprStr expected) "provider error was wrapped or reclassified as source error"
        check (next.reached == 1) "provider successor was discarded or query repeated"
  IO.println "effectful field type PASS: material/empty-prefix constructed raw constant demand; runtime error passthrough and failed-provider successor preserved (no CTFE execution claim)"
