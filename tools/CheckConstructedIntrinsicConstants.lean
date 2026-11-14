import Miri.Input.CompilerIntrinsicConstants
import Miri.Input.Decoder
open Lean Miri.Input Miri.Interpreter
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def expectInvalid [Monad m] [MonadExceptOf String m]
    (value : Except StepError A) (expected : String) : m Unit :=
  match value with
  | .error (.invalidProgram message) => unless message == expected do throw s!"wrong constant failure: {message}"
  | _ => throw "constant operation did not reject with source invariant error"
def main (args : List String) : IO Unit := do
  let [source] := args | throw (IO.userError "expected fresh const-generic fixture")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let some (definition,_) := decoded.document.definitions.zipIdx.find? (fun (definition,_) =>
      definition.rawPath.any (fun path => path.components.back?.any (·.name == some "marker")))
    | throw (IO.userError "marker source declaration absent")
  let definition ← must (initial.arena.definitionRef ⟨definition.crateIndex,definition.index⟩)
  let action : RuntimeArrayTypes.CompilerM Unit := do
    let u8 := metadata.source.queries.primitives.u8
    let value ← RuntimeArrayTypes.liftType (TypeArena.World.internConstant (.Value u8 ⟨#[.Leaf 77 1],0⟩))
    unless value >= (← get).arena.materialConstants.size do throw "constant77 was already source seeded"
    let callee ← CompilerInstance.item definition #[.Const value]
    unless callee >= (← get).instances.material.size do throw "marker77 instance was already source seeded"
    let world ← get
    match CompilerIntrinsicConstants.volatile world callee 0 with
    | .ok () => pure () | .error _ => throw "new instance Value const_at failed"
    expectInvalid (CompilerIntrinsicConstants.ordering world callee 0)
      "intrinsic generic constant: source to_branch requires a branch"
    expectInvalid (CompilerIntrinsicConstants.shuffle world callee 0)
      "intrinsic generic constant: source to_branch requires a branch"
    let parameter ← RuntimeArrayTypes.liftType (TypeArena.World.internConstant (.Param 0 "N" (some u8)))
    let nonValue ← CompilerInstance.item definition #[.Const parameter]
    expectInvalid (CompilerIntrinsicConstants.volatile (← get) nonValue 0)
      "intrinsic generic constant: source to_value requires ConstKind::Value"
  let _ ← must (action.run initial)
  IO.println "PASS const_at on genuinely new constant/instance IDs; Value/branch invariant controls fail closed"
