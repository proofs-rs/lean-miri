import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCallFacts
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unavailable symbol source accepted") | .error _ => pure ()
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine named-main snapshot")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let world ← checked (compilerEntrySeed document)
  let some material := world.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some abi := material.abi | throw (IO.userError "typed ABI source absent")
  let some names := abi.symbolNames | throw (IO.userError "typed declaration naming source absent")
  let [main] := (names.declarations.filter (·.attributes.itemName == some "main")).toList
    | throw (IO.userError "genuine main naming declaration absent")
  let key : Input.SourceCompilerWorld.InstanceKey := ⟨main.definition,#[]⟩
  let some mainId := Input.SourceCompilerWorld.findItem world key | throw (IO.userError "main canonical instance absent")
  if main.attributes.symbolName.isNone && !main.attributes.noMangle && !main.attributes.stdInternalSymbol then
    match Input.SourceCallFacts.symbolName world mainId with
    | .error "source declaration has no explicit symbol attribute" => pure ()
    | _ => throw (IO.userError "ordinary std main used a path/display or missing-source fallback")
    IO.println s!"current std naming carrier retains {names.declarations.size} declarations; ordinary mangling demand rejects"
    return
  unless (← checked (Input.SourceCallFacts.symbolName world mainId)) == "exact_main" do
    throw (IO.userError "current World did not derive raw export_name spelling")
  let [internal] := (names.declarations.filter (·.attributes.itemName == some "internal_name")).toList
    | throw (IO.userError "genuine internal-symbol declaration absent")
  unless internal.attributes.stdInternalSymbol do throw (IO.userError "genuine std-internal attribute absent")
  let key : Input.SourceCompilerWorld.InstanceKey := ⟨internal.definition,#[]⟩
  let (world,id) ← checked (Input.SourceCompilerWorld.internItem material.declarations world key)
  let (again,sameId) ← checked (Input.SourceCompilerWorld.internItem material.declarations world key)
  unless id == sameId && world.canonical.instances.size == again.canonical.instances.size do
    throw (IO.userError "same source definition did not reuse canonical instance")
  let expected := names.internalSymbolNamespace ++ "13internal_name"
  unless (← checked (Input.SourceCallFacts.symbolName world id)) == expected &&
      (← checked (Input.SourceCallFacts.symbolName again sameId)) == expected do
    throw (IO.userError "current World internal namespace spelling differs")
  let [imported] := (names.declarations.filter (·.attributes.itemName == some "imported_member")).toList
    | throw (IO.userError "genuine module import source absent")
  unless imported.foreignItem && imported.wasmImportModule == some "source_module" &&
      (← checked (Input.SourceCompilerSymbolNames.fromDeclaration names imported)) == "exact_member" do
    throw (IO.userError "native module attribute spelling differs")
  rejects (Input.SourceCompilerSymbolNames.fromDeclaration {names with isLikeWasm := true} imported)
  rejects (Input.SourceCompilerSymbolNames.fromDeclaration {names with internalSymbolNamespace := "invalid"} internal)
  let missing := {abi with symbolNames := none}
  let changed := {material with abi := some missing}
  let changed := {world with canonical := {world.canonical with sourceMaterial := some changed}}
  rejects (Input.SourceCallFacts.symbolName changed id)
  IO.println "current World exact export/internal names and canonical identity reuse pass; genuine native module and unavailable cases checked"
