import Miri.Input.SourceCompilerTypes
import Miri.Input.Decoder
import Miri.Frontend.FoundationAggregateLayout
open Miri Miri.Input Miri.Input.SourceCompilerWorld
private def expect (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "inconsistent physical pool accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: schema12-reference")
  let document := (← expect (decodeJson (← IO.FS.readFile path))).document
  let world ← expect (create document)
  let runtime ← expect ((RuntimeMetadata.ofDocument document).mapError toString)
  let some original := document.types[0]? | throw (IO.userError "compiler type absent")
  let some layout := document.layouts[original.layoutId]? | throw (IO.userError "compiler layout absent")
  let (same,id) ← expect (internType world original.shape layout "diagnostic-only spelling")
  check (id == original.id && same.canonical.types.size == world.canonical.types.size) "physical key changed by diagnostic spelling"
  rejects (internType world original.shape {layout with randomizationSeed := layout.randomizationSeed + 1} "same type")
  let aggregate ← expect (Miri.Frontend.Foundation.scalarAggregateLayout runtime.target #[layout,layout,layout] true)
  let shape := TypeShape.tuple #[original.id,original.id,original.id]
  let (next,tupleId) ← expect (internType world shape aggregate "source tuple")
  let (again,tupleId') ← expect (internType next shape aggregate "another diagnostic")
  check (tupleId == tupleId' && again.canonical.types.size == next.canonical.types.size) "demanded physical type not canonical"
  let some tuple := next.canonical.types[tupleId]? | throw (IO.userError "constructed type absent")
  check (tuple.shapeKind == .tuple && tuple.compilerFacts.isNone) "physical row fabricated compiler facts"
  check (next.canonical.instances.size == world.canonical.instances.size &&
    next.canonical.allocations.size == world.canonical.allocations.size) "physical construction changed instances/allocations"
  rejects (internType world (.tuple #[document.types.size]) aggregate "absent child")
  rejects (internType world (.adt ⟨document.definitions.size,.structKind,
    ⟨none,none,none,0,none,0⟩,#[],#[]⟩) layout "absent definition")
  let some originalDefinition := document.definitions[0]? | throw (IO.userError "compiler definition absent")
  let (withDef,defId) ← expect (internDefinition world originalDefinition)
  check (defId == 0 && withDef.canonical.definitions.size == world.canonical.definitions.size) "raw definition was renumbered"
  rejects (internDefinition world ⟨2^32,0⟩)
  IO.println "PASS canonical structural physical keys, complete layout contradictions, append-only pools and no fabricated facts"
