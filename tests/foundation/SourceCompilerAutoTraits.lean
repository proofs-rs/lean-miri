import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerAutoTraits
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported auto selection accepted")
private def change (world : Input.SourceCompilerWorld.World)
    (f : Input.SourceAbi.AutoTraits → Input.SourceAbi.AutoTraits) : Except String Input.SourceCompilerWorld.World := do
  let some source := world.canonical.sourceMaterial | throw "source absent"
  let some abi := source.abi | throw "ABI syntax absent"
  let some traits := abi.autoTraits | throw "auto source absent"
  let abi := {abi with autoTraits := some (f traits)}
  let source := {source with abi := some abi}
  return {world with canonical := {world.canonical with sourceMaterial := some source}}
def main (paths : List String) : IO Unit := do
  let [sourcePath,oraclePath] := paths | throw (IO.userError "expected genuine std source and projected compiler oracle")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile sourcePath))))
  let initial ← checked (compilerEntrySeed document)
  let some start := initial.canonical.instances[1]? | throw (IO.userError "selected start absent")
  let (world,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody initial start.id)
  let some closure := world.canonical.types.find? (·.shapeKind == .closure) | throw (IO.userError "actual closure absent")
  let .closure definition arguments count := closure.shape | throw (IO.userError "closure source shape absent")
  let some raw := world.canonical.definitions[definition]? | throw (IO.userError "closure raw identity absent")
  let some (.Type tuple) := arguments.back? | throw (IO.userError "capture tuple absent")
  let some tupleNode := world.canonical.types[tuple]? | throw (IO.userError "capture tuple missing")
  let .tuple captures := tupleNode.shape | throw (IO.userError "captures not tuple")
  unless captures.size == count do throw (IO.userError "capture source count mismatch")
  let oracle ← checked (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← checked (oracle.getObjValAs? (Array Json) "closures")
  let matching ← checked (rows.filterM fun row => do
    return (← row.getObjValAs? Nat "crate_index") == raw.crateIndex && (← row.getObjValAs? Nat "index") == raw.index)
  let [reference] := matching.toList | throw (IO.userError "independent closure oracle absent/ambiguous")
  for (role,key) in #[(Input.SourceAbi.AutoTraitRole.unpin,"is_unpin"),(.unsafeUnpin,"is_unsafe_unpin"),(.freeze,"is_freeze")] do
    let actual ← checked (Input.SourceCompilerAutoTraits.check world role closure.id)
    let expected ← checked (reference.getObjValAs? Bool key)
    unless actual == expected do throw (IO.userError s!"compiler contrast differs: {key}")
    let incomplete ← checked (change world fun traits => {traits with declarations := traits.declarations.map (fun declaration => {declaration with complete := false})})
    rejects (Input.SourceCompilerAutoTraits.check incomplete role closure.id)
    let unknown ← checked (change world fun traits => {traits with declarations := traits.declarations.map (fun declaration =>
      {declaration with implementations := declaration.implementations.push ⟨raw,.unknown,"Negative"⟩})})
    rejects (Input.SourceCompilerAutoTraits.check unknown role closure.id)
    let competing ← checked (change world fun traits => {traits with declarations := traits.declarations.map (fun declaration =>
      {declaration with implementations := declaration.implementations.push ⟨raw,.closure raw,"Negative"⟩})})
    rejects (Input.SourceCompilerAutoTraits.check competing role closure.id)
    let mislabeled ← checked (change world fun traits => {traits with declarations := traits.declarations.map (fun declaration => {declaration with langItem := none})})
    rejects (Input.SourceCompilerAutoTraits.check mislabeled role closure.id)
    let ordinary ← checked (change world fun traits => {traits with declarations := traits.declarations.map (fun declaration => {declaration with isAuto := false})})
    rejects (Input.SourceCompilerAutoTraits.check ordinary role closure.id)
    let missing ← checked (change world fun traits => {traits with declarations := #[]})
    rejects (Input.SourceCompilerAutoTraits.check missing role closure.id)
    unless (← checked (Input.SourceCompilerAutoTraits.check missing role tuple)) do
      throw (IO.userError "pinned trivial capture tuple fastpath incorrectly demanded auto headers")
  IO.println "actual std closure: Unpin/UnsafeUnpin/Freeze match independent compiler; complete manual exclusion and capture obligations; missing/ambiguous negative evidence rejects"
