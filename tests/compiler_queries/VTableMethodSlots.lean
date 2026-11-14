import Miri.Input.Decoder
import Miri.Input.WorldVTableMethods
open Lean Miri.Input GenericSubstitution TraitSelection
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def expectedSlot (row : Json) : Except String WorldVTableMethods.Slot := do
  let kind ← (← row.getObjVal? "kind").getStr?
  if kind == "vacant" then return .vacant
  let identity ← GenericMaterialCodec.readDefinition (← row.getObjVal? "definition")
  let arguments ← (← (← row.getObjVal? "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 2048)
  let method : WorldVTableMethods.SelectedDeclaration := ⟨identity,arguments⟩
  match kind with
  | "selected" => pure (.selected method)
  | "by_value_shim" => pure (.byValueShim method)
  | _ => throw "unknown independent oracle slot kind"
private def slots (document : ImportDocument) (reference : TraitRef) := do
  WorldVTableMethods.ownSlots (← AliasRuntime.Context.ofDocument document) 100000 2048 reference
private def reject (document : ImportDocument) (reference : TraitRef) (message : String) : IO Unit := do
  match slots document reference with
  | .ok _ => throw (IO.userError s!"missing method header accepted: {message}")
  | .error actual => unless actual == message do throw (IO.userError s!"wrong rejection: {actual}; expected {message}")
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source and oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with compilerPredicates := #[], instances := #[], allocations := #[], functionAbis := #[], queries := {original.queries with runtime := {original.queries.runtime with virtualQueries := #[]}, vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  unless rows.size == 4 do throw (IO.userError "oracle coverage changed")
  let mut total := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let reference ← must (TraitSelection.Codec.readTraitRef (← must (row.getObjVal? "reference")))
    let expected ← must ((← must ((← must (row.getObjVal? "entries")).getArr?)).mapM expectedSlot)
    let actual ← must (slots document reference)
    unless actual == expected do throw (IO.userError s!"raw slots differ from pinned rustc: {name}")
    unless actual.size == 4 do throw (IO.userError "own slot count changed")
    total := total + actual.size
    IO.println s!"PASS {name}: complete raw slot identity, kind and arguments"
    if name == "query_none" then
      unless actual.all (· == .vacant) do throw (IO.userError "absent concrete impl must make every slot Vacant")
      continue
    let some (WorldVTableMethods.Slot.selected first) := actual[0]? | throw (IO.userError "first method not selected")
    let change (f : DefinitionId → DefinitionId) := {document with definitions := document.definitions.map fun source =>
      if source.crateIndex == first.definition.crateIndex && source.index == first.definition.index then f source else source}
    reject (change fun source => {source with sourceEnvironment := none}) reference "raw source environment declaration is absent"
    reject (change fun source => {source with genericTemplate := none}) reference "vtable method source template absent"
    reject (change fun source => {source with genericTemplate := source.genericTemplate.map fun template =>
      {template with signatureExpression := none}}) reference "vtable method raw signature absent"
    reject (change fun source => {source with sourceEnvironment := source.sourceEnvironment.map fun scope =>
      {scope with parent := none}}) reference "vtable method source parent mismatch"
  unless total == 16 do throw (IO.userError "oracle total changed")
  IO.println "PASS 16 actual raw slots, including absent-impl by-value negative and erased parent lifetimes; all predicate/vtable/ABI/instance/allocation answer rows erased; 12 missing-header controls"
