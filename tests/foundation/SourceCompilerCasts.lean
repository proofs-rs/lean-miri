import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerCasts
import Miri.Input.CompilerPlaceTypes
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unavailable source cast query accepted") | .error _ => pure ()

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let runtime ← checked ((Input.RuntimeMetadata.ofDocument world.canonical).mapError toString)
  let some closure := world.canonical.types.find? (fun node => node.shapeKind == .closure)
    | throw (IO.userError "genuine closure type absent")
  let some dynamic := world.canonical.types.find? (fun node => node.shapeKind == .dynamicTraitObject)
    | throw (IO.userError "genuine dyn type absent")
  unless (← checked (Input.SourceCompilerCasts.lockstepTails world closure.id dynamic.id)) == (closure.id,dynamic.id) do
    throw (IO.userError "closure/dyn tails must stop without catalog")
  let .closure _ args count := closure.shape | throw (IO.userError "closure shape absent")
  let some (.Type upvars) := args.back? | throw (IO.userError "tupled upvars argument absent")
  let some tuple := world.canonical.types[upvars]? | throw (IO.userError "upvars type absent")
  let .tuple fields := tuple.shape | throw (IO.userError "upvars tuple absent")
  unless fields.size == count && count > 0 do throw (IO.userError "nonempty genuine capture domain absent")
  let some tail := fields.back? | throw (IO.userError "tuple tail absent")
  unless (← checked (Input.SourceCompilerCasts.structTail world upvars)) == tail do
    throw (IO.userError "source struct_tail tuple descent differs")
  unless (← checked (Input.SourceCompilerCasts.lockstepTails world upvars upvars)) == (tail,tail) do
    throw (IO.userError "equal tuple IDs must still descend")
  let layout ← checked ((runtime.lookup closure.id).mapError toString)
  for index in [:count] do
    let field ← checked ((runtime.field layout index).mapError toString)
    unless fields[index]? == some field.ty do throw (IO.userError "closure field type differs from source upvars")
  rejects ((runtime.field layout count).mapError toString)
  let .closure .. ← checked (Input.SourceCompilerCasts.typeInfo runtime closure.id)
    | throw (IO.userError "current cast closure classification absent")
  let .dynamic predicates ← checked (Input.SourceCompilerCasts.typeInfo runtime dynamic.id)
    | throw (IO.userError "current cast dyn classification absent")
  unless !predicates.isEmpty do throw (IO.userError "dynamic predicate identity lost")
  checked (Input.SourceCompilerCasts.ensureMonomorphic world closure.id)
  checked (Input.SourceCompilerCasts.ensureMonomorphic world dynamic.id)
  let some reference := world.canonical.types.find? (fun node => match node.shape with
    | .reference pointee .. => pointee == closure.id | _ => false)
    | throw (IO.userError "closure reference absent")
  unless (← checked (Input.SourceCompilerCasts.builtinDeref world reference.id false)) == some closure.id do
    throw (IO.userError "current builtin reference dereference mismatch")
  rejects (Input.SourceCompilerCasts.lockstepTails world world.canonical.types.size dynamic.id)
  unless initial.canonical.queries.casts.isEmpty do throw (IO.userError "fixture unexpectedly supplies cast answers")
  IO.println "source World closure/dyn and tuple lockstep, current cast kinds, closure fields, monomorphism and reference dereference pass without cast catalogs"
