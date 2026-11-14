import Miri.Input.Decoder
import Miri.Input.CompilerProviders
import Miri.Input.CompilerWorldCompatibility
open Lean Miri.Input Miri.Interpreter TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ next => next⟩
private def run (world : RuntimeArrayTypes.World) (action : EStateM StepError RuntimeArrayTypes.World A) : IO (A × RuntimeArrayTypes.World) :=
  match action world with
  | .ok value next => pure (value,next)
  | .error error _ => throw (IO.userError (reprStr error))
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected raw alias source fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let prepared ← must (CompilerProviders.prepare (← must (lowerProgram document)))
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let empty ← must (World.ofMaterial #[] #[] document.definitions #[] initial.arena.pointerBytes)
  let mut world := {initial with arena := empty}
  let q := CompilerWorldCompatibility.queries prepared.lifecycle.calls.symbols.facts.context access
  let mut records := #[]
  let mut aliases := 0
  for node in document.types do
    if let .adt shape := node.shape then
      let some definition := document.definitions[shape.definition]? | continue
      let some name := definition.rawPath.bind (fun path => path.components.back?.bind (·.name)) | continue
      if name != "Record" then continue
      let term ← must (GenericInstantiationWorld.ofType initial.arena 16384 node.id)
      let (ty,next) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 term)).run world)
      world := next
      let (info,next) ← run world (q.adt ty)
      world := next
      let some fields := info.variants[0]? | throw (IO.userError "Record has no variant")
      let some field := fields[0]? | throw (IO.userError "Record has no field")
      check (field.name == "value") "Record raw field symbol changed"
      if let .constructed (.alias ..) ← must (world.arena.lookupType field.ty) then
        aliases := aliases + 1
        let (normalized,next) ← run world (q.normalize field.ty)
        world := next
        let .constructed (.integer false .u32) ← must (world.arena.lookupType normalized)
          | throw (IO.userError "associated field did not separately normalize to u32")
        let .constructed (.alias ..) ← must (world.arena.lookupType field.ty)
          | throw (IO.userError "normalization overwrote raw alias field identity")
      records := records.push ty
  check (records.size == 2 && aliases == 1) "raw ADTinfo normalized the alias eagerly or omitted source records"
  let (identical,after) ← run world (LayoutCompat.identicalCTypes q 256 records[0]! records[1]!)
  check identical "source identicalCTypes failed separate field normalization"
  check (after.arena.materialTypes.isEmpty && after.arena.materialConstants.isEmpty && after.arena.materialPredicates.isEmpty)
    "source compatibility acquired closed prefixes"
  IO.println "PASS one raw alias retained in ADTinfo, separately normalized u32; distinct physical C Records compare identical through source algorithm with empty prefixes"
