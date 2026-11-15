import Miri.Frontend.FoundationSourceTypes
import Miri.Input.SourcePhysical
import Miri.Input.CatalogDecoderRuntime
import Miri.Input.TableTail
open Lean Miri Miri.Input Miri.Input.SourceTypes
private def expect (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unsupported typed physical source accepted")
def main (paths : List String) : IO Unit := do
  let [sourcePath,oraclePath] := paths | throw (IO.userError "usage: source projected-compiler-oracle")
  let raw ← expect (Json.parse (← IO.FS.readFile sourcePath))
  let source ← expect (Frontend.Foundation.SourceTypesParser.material raw)
  let targetSource ← expect (raw.getObjVal? "target" >>= fun t => t.getObjVal? "runtime_data_layout")
  let targetSource ← expect (JsonReader.run CatalogDecoder.targetDataLayout targetSource.compress)
  let target ← expect ((RuntimeMetadata.importTarget targetSource).mapError toString)
  let oracle ← expect (Json.parse (← IO.FS.readFile oraclePath))
  let expected ← expect (oracle.getObjValAs? (Array Json) "local_layouts")
  let bodies ← expect (raw.getObjValAs? (Array Json) "bodies")
  let some body := bodies[0]? | throw (IO.userError "source body absent")
  let locals ← expect (body.getObjValAs? (Array Nat) "locals")
  check (locals.size == expected.size && locals.size == 7) "source local coverage"
  for (id,i) in locals.zipIdx do
    let concrete ← expect (instantiate source #[] #[] id >>= eraseRegions)
    let layout ← expect (SourcePhysical.calculate source target concrete)
    let actual ← expect ((RuntimeMetadata.layout target layout).mapError toString)
    let some row := expected[i]? | throw (IO.userError "compiler row absent")
    let row ← expect (JsonReader.run DecoderValues.decodeCompilerLayout row.compress)
    let compiler ← expect ((RuntimeMetadata.layout target row).mapError toString)
    check (actual == compiler) s!"complete typed std local{i} layout differs"
  let some closureRef := locals[6]? | throw (IO.userError "closure local absent")
  let closure ← expect (instantiate source #[] #[] closureRef >>= eraseRegions)
  let .closure _ args := closure | throw (IO.userError "typed closure shape")
  let some (.tuple fields) := args.back? | throw (IO.userError "typed capture tuple")
  let tuple ← expect (SourcePhysical.calculate source target (.tuple fields))
  let tuple ← expect ((RuntimeMetadata.layout target tuple).mapError toString)
  let tupleExpected ← expect (oracle.getObjVal? "capture_tuple_layout")
  let tupleExpected ← expect (JsonReader.run DecoderValues.decodeCompilerLayout tupleExpected.compress)
  let tupleExpected ← expect ((RuntimeMetadata.layout target tupleExpected).mapError toString)
  check (tuple == tupleExpected) "complete typed MaybeUnsized tuple layout differs"
  let some dynRef := locals[1]? | throw (IO.userError "dyn ref absent")
  let dynType ← expect (instantiate source #[] #[] dynRef >>= eraseRegions)
  rejects (SourcePhysical.calculate {source with dynMetadata := none} target dynType)
  rejects (SourcePhysical.calculate source target (.tuple (fields.extract 0 2)))
  IO.println "PASS typed-only source target/types to all7 complete std layouts and tuple; unsupported metadata/aggregate controls"
