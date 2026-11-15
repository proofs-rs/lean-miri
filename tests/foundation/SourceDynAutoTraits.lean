import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerAutoTraits
import Miri.Input.SourceCompilerTypes
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unproved dyn auto trait accepted") | .error _ => pure ()
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  if (← checked (entrySelection document.source)).compilerEntry.isNone then
    let abi ← checked (SourceAbiParser.material document)
    let physical ← checked (SourceTypesParser.material document.source)
    let mut localObjects := 0
    for type in physical.types do
      if let .dynamicObject _ predicates := type then
        let mut principal := none
        let mut autoBounds := #[]
        for predicate in predicates do
          match predicate with
          | .trait definition .. =>
            let some row := physical.definitions[definition]? | throw (IO.userError "object principal declaration absent")
            unless principal.isNone do throw (IO.userError "object principal duplicated")
            principal := some row.raw
          | .autoTrait definition .. =>
            let some row := physical.definitions[definition]? | throw (IO.userError "auto bound declaration absent")
            autoBounds := autoBounds.push row.raw
          | .projection .. => pure ()
          | .unsupported tag => throw (IO.userError tag)
        if principal.any (·.crateIndex == 0) then
          localObjects := localObjects + 1
          for role in #[Input.SourceAbi.AutoTraitRole.unpin,.unsafeUnpin,.freeze] do
            unless !(← checked (Input.SourceCompilerAutoTraits.checkObjectBounds abi role principal autoBounds)) do
              throw (IO.userError "local principal acquired absent auto role")
            rejects (Input.SourceCompilerAutoTraits.checkObjectBounds {abi with objectTraits := #[]} role principal autoBounds)
    unless localObjects > 0 do throw (IO.userError "genuine non-Fn local principal absent")
    IO.println "genuine local principal/supertrait graph excludes all three auto roles; missing graph rejects"
    return
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let some object := world.canonical.types.find? (fun row => match row.shape with | .dynamicTraitObject .. => true | _ => false)
    | throw (IO.userError "genuine dynamic object absent")
  let .dynamicTraitObject predicates principal region := object.shape | throw (IO.userError "dynamic shape absent")
  let some material := world.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some abi := material.abi | throw (IO.userError "typed ABI source absent")
  let some auto := abi.autoTraits | throw (IO.userError "auto declaration source absent")
  unless abi.objectTraits.size > 0 do throw (IO.userError "supertrait graph absent")
  for role in #[Input.SourceAbi.AutoTraitRole.unpin,.unsafeUnpin,.freeze] do
    unless !(← checked (Input.SourceCompilerAutoTraits.check world role object.id)) do
      throw (IO.userError "genuine object acquired an absent auto bound")
    let some declaration := auto.declarations.find? (·.langItem == some role)
      | throw (IO.userError "queried role declaration absent")
    -- A unit control for the exact explicit-bound rule, using the actual role
    -- declaration and ordinary canonical interners, not a selected answer row.
    let (explicitWorld,definition) ← checked (Input.SourceCompilerWorld.internDefinition world declaration.definition)
    let (explicitWorld,predicate) ← checked (Input.SourceCompilerWorld.internPredicate explicitWorld {
      kind := .autoTrait,definitionId := definition,definitionPath := none,genericArgs := #[],boundVariables := #[],projectionTerm := none })
    let some layout := explicitWorld.canonical.layouts[object.layoutId]? | throw (IO.userError "genuine dynamic layout absent")
    let (explicitWorld,type) ← checked (Input.SourceCompilerWorld.internType explicitWorld
      (.dynamicTraitObject (predicates.push predicate) principal region) layout "explicit auto-bound control")
    unless (← checked (Input.SourceCompilerAutoTraits.check explicitWorld role type)) do
      throw (IO.userError "exact explicit auto bound was not recognized")
    let missingGraph := {abi with objectTraits := #[]}
    let changedMaterial := {material with abi := some missingGraph}
    let changed := {world with canonical := {world.canonical with sourceMaterial := some changedMaterial}}
    rejects (Input.SourceCompilerAutoTraits.check changed role object.id)
    let unsupportedGraph := abi.objectTraits.map fun row => {row with unsupportedSuperClauses := #["unknown"]}
    let changedMaterial := {material with abi := some {abi with objectTraits := unsupportedGraph}}
    let changed := {world with canonical := {world.canonical with sourceMaterial := some changedMaterial}}
    rejects (Input.SourceCompilerAutoTraits.check changed role object.id)
    let cycleGraph := abi.objectTraits.map fun row => {row with superTraits := #[row.definition]}
    let changedMaterial := {material with abi := some {abi with objectTraits := cycleGraph}}
    let changed := {world with canonical := {world.canonical with sourceMaterial := some changedMaterial}}
    rejects (Input.SourceCompilerAutoTraits.check changed role object.id)
    if let some header := declaration.implementations[0]? then
      let ambiguous := {declaration with implementations := declaration.implementations.push {header with selfHead := .unknown}}
      let auto := {auto with declarations := auto.declarations.map fun row => if row.definition == declaration.definition then ambiguous else row}
      let changedMaterial := {material with abi := some {abi with autoTraits := some auto}}
      let changed := {explicitWorld with canonical := {explicitWorld.canonical with sourceMaterial := some changedMaterial}}
      rejects (Input.SourceCompilerAutoTraits.check changed role type)
  IO.println "genuine dyn object excludes all three auto roles; exact explicit bounds succeed; incomplete graph rejects"
