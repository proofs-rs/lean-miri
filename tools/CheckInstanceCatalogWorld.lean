import Miri.Input.CompilerInstanceAbi
import Miri.Input.CompilerNativeSignatures
import Miri.Input.Decoder
open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def expect (value : Except String A) (expected : String) : IO Unit :=
  match value with
  | .error message => unless message == expected do throw (IO.userError s!"wrong catalog guard: {message}")
  | .ok _ => throw (IO.userError "instance catalog silently reused a numeric identity from another store")
def main (args : List String) : IO Unit := do
  let [source] := args | throw (IO.userError "expected novel-instance-call fixture")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let document := decoded.document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let program ← must (lowerProgram document)
  let prepared ← must (CompilerInstanceAbi.prepare runtime program)
  let native ← must (CompilerProviders.prepare program)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let _ ← must (CompilerInstanceAbi.abiOfInstance prepared world 3 #[])
  let _ ← must (CompilerInstanceAbi.abiOfInstance prepared world 4 #[])
  let _ ← must (CompilerNativeSignatures.query native world 3)
  let _ ← must (CompilerNativeSignatures.query native world 4)
  let some other := document.instances[4]? | throw (IO.userError "fixture lacks distinct source instance4")
  let material ← must (InstanceArena.Store.ofSource world.arena (document.instances.extract 0 3))
  let key ← must (InstanceArena.Key.ofSource world.arena other.instanceKind other.genericArgs)
  let (id,constructed) ← must (material.intern world.arena key)
  unless id == 3 do throw (IO.userError "fixture fails to create numeric instance collision3")
  expect (CompilerInstanceAbi.abiOfInstance prepared {world with instances := constructed} id #[])
    "constructed instance has no imported FnAbi query"
  expect (CompilerNativeSignatures.query native {world with instances := constructed} id)
    "constructed instance has no imported native signature query"
  let material ← must (InstanceArena.Store.ofSource world.arena
    ((document.instances.extract 0 3).push {other with id := 3}))
  expect (CompilerInstanceAbi.abiOfInstance prepared {world with instances := material} 3 #[])
    "instance ABI source material differs from execution instance store"
  expect (CompilerNativeSignatures.query native {world with instances := material} 3)
    "native signature source material differs from execution instance store"
  IO.println "PASS actual leaf<u64>/leaf<u32> ABI/native catalog collisions rejected for constructed and mismatched material stores"
