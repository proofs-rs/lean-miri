import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerVTables
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unavailable source retag query accepted") | .error _ => pure ()

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let some closure := world.canonical.types.find? (fun row => match row.shape with | .closure .. => true | _ => false)
    | throw (IO.userError "genuine selected closure absent")
  let some dynamic := world.canonical.types.find? (fun row => match row.shape with | .dynamicTraitObject .. => true | _ => false)
    | throw (IO.userError "genuine selected dynamic object absent")
  let .dynamicTraitObject predicates _ _ := dynamic.shape | throw (IO.userError "dynamic shape absent")
  let pair ← checked (Input.SourceCompilerVTables.erasedPair world closure.id predicates)
  unless pair == (closure.id,predicates) do throw (IO.userError "region-free pair identity changed")
  let _ ← checked (Input.SourceCompilerVTables.ensureMonomorphicPredicates world predicates)
  let comparison ← checked (Input.SourceCompilerVTables.comparisonPredicates world predicates)
  let expected := predicates.filter (fun id => match world.canonical.predicates[id]? with
    | some row => row.kind != .autoTrait | none => false)
  unless comparison.map (·.id) == expected && comparison.all (!·.autoTrait) do
    throw (IO.userError "source comparison did not remove exactly the auto traits")
  for value in comparison do
    unless (← checked (Input.SourceCompilerVTables.normalizeComparisonPredicate world value)) == value.id do
      throw (IO.userError "alias-free erased predicate normalization changed identity")
  let some projectionId := predicates.find? (fun id => match world.canonical.predicates[id]? with
    | some row => row.kind == .projection | none => false)
    | throw (IO.userError "genuine associated projection absent")
  let some projection := world.canonical.predicates[projectionId]? | throw (IO.userError "projection absent")
  let some traitId := predicates.find? (fun id => match world.canonical.predicates[id]? with
    | some row => row.kind == .trait | none => false)
    | throw (IO.userError "genuine principal absent")
  let some principal := world.canonical.predicates[traitId]? | throw (IO.userError "principal absent")
  let distinct := world.canonical.predicates.push {projection with definitionId := principal.definitionId}
  let changed := {world with canonical := {world.canonical with predicates := distinct}}
  rejects (Input.SourceCompilerVTables.comparisonPredicates changed #[projectionId,world.canonical.predicates.size])
  rejects (Input.SourceCompilerVTables.normalizeComparisonPredicate world ⟨traitId,1,false⟩)
  rejects (Input.SourceCompilerVTables.normalizeComparisonPredicate world ⟨traitId,0,true⟩)
  rejects (Input.SourceCompilerVTables.erasedPair world world.canonical.types.size predicates)
  rejects (Input.SourceCompilerVTables.erasedPair world closure.id #[world.canonical.predicates.size])
  let .closure definition arguments count := closure.shape | throw (IO.userError "closure shape absent")
  let altered := {closure with shape := .closure definition (arguments.push (.Lifetime .Static)) count}
  let types ← if h : closure.id < world.canonical.types.size then pure (world.canonical.types.set closure.id altered h)
    else throw (IO.userError "closure handle absent")
  let changed := {world with canonical := {world.canonical with types}}
  rejects (Input.SourceCompilerVTables.erasedPair changed closure.id predicates)
  let some predicateId := predicates[0]? | throw (IO.userError "predicate absent")
  let some predicate := world.canonical.predicates[predicateId]? | throw (IO.userError "predicate handle absent")
  let predicateRows ← if h : predicateId < world.canonical.predicates.size then
      pure (world.canonical.predicates.set predicateId {predicate with boundVariables := #[.Const]} h)
    else throw (IO.userError "predicate handle absent")
  let changed := {world with canonical := {world.canonical with predicates := predicateRows}}
  rejects (Input.SourceCompilerVTables.erasedPair changed closure.id predicates)
  rejects (Input.SourceCompilerVTables.normalizeComparisonPredicate changed ⟨predicateId,0,false⟩)
  IO.println "genuine region-free closure/predicate pair preserved; missing handles, static regions and binders reject"
