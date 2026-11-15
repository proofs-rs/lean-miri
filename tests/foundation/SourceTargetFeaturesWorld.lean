import Miri.Frontend.FoundationEntrySeed
import Miri.Input.CompilerTargetFeatures
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "missing feature declaration accepted") | .error _ => pure ()
def main (paths : List String) : IO Unit := do
  let [stdPath,closurePath] := paths | throw (IO.userError "expected actual std snapshot and inherited-feature closure")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile stdPath))))
  let world ← checked (compilerEntrySeed document)
  for node in world.canonical.instances do
    unless (← checked (Input.CompilerTargetFeatures.requiredSource world node.id)).isEmpty do
      throw (IO.userError "genuine std source feature declaration differs")
  let some source := world.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some abi := source.abi | throw (IO.userError "typed feature declarations absent")
  let missing := {abi with targetFeatureDeclarations := #[]}
  let changedSource := {source with abi := some missing}
  let changed := {world with canonical := {world.canonical with sourceMaterial := some changedSource}}
  for node in world.canonical.instances do rejects (Input.CompilerTargetFeatures.requiredSource changed node.id)
  let closureDoc ← checked (decode (← checked (Json.parse (← IO.FS.readFile closurePath))))
  let closureAbi ← checked (SourceAbiParser.material closureDoc)
  let templates ← checked (closureDoc.source.getObjValAs? (Array Json) "closure_templates")
  unless !templates.isEmpty do throw (IO.userError "genuine inherited-feature closure absent")
  for closure in templates do
    let definition ← checked (closure.getObjValAs? Nat "definition")
    let parent ← checked (closure.getObjValAs? Nat "parent_definition")
    let raw (id : Nat) : IO Input.DefinitionId := do
      let some row := closureDoc.definitions[id]? | throw (IO.userError "closure source definition absent")
      return ⟨← checked (row.getObjValAs? Nat "crate_index"),← checked (row.getObjValAs? Nat "index")⟩
    let definition ← raw definition
    let parent ← raw parent
    let features ← checked (Input.CompilerTargetFeatures.requiredOfDefinition closureAbi definition)
    let inherited ← checked (Input.CompilerTargetFeatures.requiredOfDefinition closureAbi parent)
    unless !features.isEmpty && features.map (fun value => (value.name,value.implied)) ==
        inherited.map (fun value => (value.name,value.implied)) do
      throw (IO.userError "closure target features did not preserve actual parent inheritance")
    unless !(closureAbi.functions.any (·.definition == definition)) do
      throw (IO.userError "closure feature declaration invented a function signature")
  IO.println "current std World features read source declarations; closure inherits real nonempty features without fabricated FnSig; missing source rejects"
