import Miri.Frontend.FoundationSourceTypes
import Miri.Input.SourcePhysical
import Miri.Input.CatalogDecoderRuntime
import Miri.Input.TableTail
open Lean Miri Miri.Input Miri.Input.SourceTypes
private def expect (r : Except String α) : IO α := match r with
  | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "usage: source compiler-reference")
  let raw ← expect (Json.parse (← IO.FS.readFile sourcePath))
  let source ← expect (Frontend.Foundation.SourceTypesParser.material raw)
  let targetSource ← expect (raw.getObjVal? "target" >>= fun t => t.getObjVal? "runtime_data_layout")
  let targetSource ← expect (JsonReader.run CatalogDecoder.targetDataLayout targetSource.compress)
  let target ← expect ((RuntimeMetadata.importTarget targetSource).mapError toString)
  let reference ← expect (Json.parse (← IO.FS.readFile referencePath))
  let bodies ← expect (raw.getObjValAs? (Array Json) "bodies")
  let some body := bodies[0]? | throw (IO.userError "source body absent")
  let locals ← expect (body.getObjValAs? (Array Nat) "locals")
  let referenceBodies ← expect (reference.getObjValAs? (Array Json) "bodies")
  let some referenceBody := referenceBodies[0]? | throw (IO.userError "compiler body absent")
  let referenceLocals ← expect (referenceBody.getObjValAs? (Array Json) "locals")
  let types ← expect (reference.getObjValAs? (Array Json) "types")
  let layouts ← expect (reference.getObjValAs? (Array Nat) "layouts")
  let values ← expect (reference.getObjValAs? (Array Json) "layout_values")
  check (locals.size == 8 && referenceLocals.size == locals.size) "fixture union coverage"
  for (typeRef,i) in locals.zipIdx do
    let concrete ← expect (instantiate source #[] #[] typeRef >>= eraseRegions)
    let layout ← expect (SourcePhysical.calculate source target concrete)
    let actual ← expect ((RuntimeMetadata.layout target layout).mapError toString)
    let some localRow := referenceLocals[i]? | throw (IO.userError "compiler local absent")
    let typeId ← expect (localRow.getObjValAs? Nat "type")
    let some type := types[typeId]? | throw (IO.userError "compiler type absent")
    let layoutId ← expect (type.getObjValAs? Nat "layout")
    let some valueId := layouts[layoutId]? | throw (IO.userError "compiler layout absent")
    let some row := values[valueId]? | throw (IO.userError "compiler layout value absent")
    let row ← expect (JsonReader.run DecoderValues.decodeCompilerLayout row.compress)
    let compiler ← expect ((RuntimeMetadata.layout target row).mapError toString)
    check (actual == compiler) s!"complete union local{i} layout differs: actual={reprStr actual} compiler={reprStr compiler}"
  let some unionRef := locals[1]? | throw (IO.userError "union local absent")
  let concrete ← expect (instantiate source #[] #[] unionRef >>= eraseRegions)
  let .nominal definition _ := concrete | throw (IO.userError "union nominal absent")
  let some declaration := source.definitions[definition]? | throw (IO.userError "union declaration absent")
  let some adt := declaration.adt | throw (IO.userError "union ADT absent")
  let some variant := adt.variants[0]? | throw (IO.userError "union variant absent")
  let empty := {adt with variants := #[{variant with fields := #[]}]}
  let badFlags := {adt with representation := {adt.representation with flagsBits := 2}}
  let zeroAlign := {adt with representation := {adt.representation with alignBytes := some 0}}
  let invalidPack := {adt with representation := {adt.representation with packBytes := some 3}}
  for (invalid,index) in (#[empty,badFlags,{adt with variants := #[]},zeroAlign,invalidPack]).zipIdx do
    let changed ← if h : definition < source.definitions.size then
      pure {source with definitions := source.definitions.set definition {declaration with adt := some invalid} h}
      else throw (IO.userError "union definition index absent")
    match SourcePhysical.calculate changed target concrete with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid union accepted: control {index}")
  IO.println "PASS seven complete compiler union layouts: mixed/scalar/pair/C/packed/aligned/generic; empty/flags/variant/invalid-alignment negatives"
