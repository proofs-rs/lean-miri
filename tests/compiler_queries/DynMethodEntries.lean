import Miri.Input.Decoder
import Miri.Input.WorldDynMethods

open Lean Miri.Input GenericSubstitution TraitSelection
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def query (document : ImportDocument) (identity : DefinitionIdentity) : Except String (Array DefinitionIdentity) := do
  WorldDynMethods.ownMethods (← AliasRuntime.Context.ofDocument document) 100000 2048 identity
private def reject (document : ImportDocument) (identity : DefinitionIdentity) (expected : String) : IO Unit := do
  match query document identity with
  | .ok _ => throw (IO.userError "malformed dyn source material was accepted")
  | .error actual => unless actual == expected do throw (IO.userError s!"unexpected dyn material rejection: {actual}")

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh raw source and independent dyn-method oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with compilerPredicates := #[], queries := {original.queries with vtables := #[]}}
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let methods ← must ((← must (oracle.getObjVal? "source_methods")).getArr?)
  let expected ← must ((← must ((← must (oracle.getObjVal? "oracle_own_entries")).getArr?)).mapM GenericMaterialCodec.readDefinition)
  unless methods.size == 10 && expected.size == 5 do throw (IO.userError "dyn method oracle coverage changed")
  let identities ← must (methods.mapM fun row => do GenericMaterialCodec.readDefinition (← row.getObjVal? "definition"))
  let sources := document.traitProgram.traits.filter fun source => source.members.any (identities.contains ·.definition)
  unless sources.size == 1 do throw (IO.userError "dyn oracle source trait identity ambiguous")
  let some source := sources[0]? | throw (IO.userError "dyn oracle source trait absent")
  let actual ← must (query document source.definition)
  unless actual == expected do throw (IO.userError "source dyn own entries/order differ from pinned rustc")
  -- Exercise the same provider through the current execution-owned World.
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create metadata).mapError (fun error => reprStr error))
  let (worldActual,_) ← must ((WorldDynMethods.query source.definition 100000 2048).run world)
  unless worldActual == expected do throw (IO.userError "World dyn own entries differ from pinned rustc")
  for row in methods do
    let identity ← must (GenericMaterialCodec.readDefinition (← must (row.getObjVal? "definition")))
    let members := source.members.filter (·.definition == identity)
    let some member := members[0]? | throw (IO.userError "canonical raw dyn member absent")
    unless members.size == 1 do throw (IO.userError "canonical raw dyn member duplicated")
    let isMethod ← must ((← must (row.getObjVal? "is_method")).getBool?)
    let isFinal ← must ((← must (row.getObjVal? "is_final")).getBool?)
    unless member.isMethod == isMethod && member.isFinal == isFinal do
      throw (IO.userError "canonical raw member flags differ from independent source declaration")
  let some owner := identities[0]? | throw (IO.userError "positive dyn member identity absent")
  let modify (change : DefinitionId → DefinitionId) := fun (input : ImportDocument) =>
    {input with definitions := input.definitions.map fun definition =>
      if definition.crateIndex == owner.crateIndex && definition.index == owner.index then change definition else definition}
  let missing := modify (fun source => {source with sourceEnvironment := none}) document
  reject missing source.definition "raw source environment declaration is absent"
  let missingSignature := modify (fun source => {source with genericTemplate := source.genericTemplate.map fun template =>
    {template with signatureExpression := none}}) document
  reject missingSignature source.definition "dyn method raw function signature absent"
  let pollutedScope := modify (fun source => {source with sourceEnvironment := source.sourceEnvironment.map fun scope =>
    {scope with ownPredicates := #[⟨#[],.equal (.placeholder .type 1 0 .anonymous) (.placeholder .type 1 0 .anonymous)⟩]}}) document
  reject pollutedScope source.definition "placeholder forbidden for this generic syntax role"
  let pollutedSignature := modify (fun source => {source with genericTemplate := source.genericTemplate.map fun template =>
    {template with signatureExpression := template.signatureExpression.map fun signature =>
      match signature with
      | .binder variables (.node sort tag payload children) =>
        let values := AliasNormalization.termsToArray children
        .binder variables (.node sort tag payload (Terms.ofArray
          (values.pop.push (.placeholder .type 1 0 .anonymous))))
      | other => other}}) document
  reject pollutedSignature source.definition "placeholder forbidden for this generic syntax role"
  let some dispatch := document.traitProgram.traits.find? (·.langItem == some "dispatch_from_dyn")
    | throw (IO.userError "raw DispatchFromDyn declaration absent")
  let some referenceImpl := dispatch.implementations.find? (fun implementation =>
    match implementation.traitRef.arguments[0]? with
    | some (.node .type "reference" "immutable" _) => true
    | _ => false)
    | throw (IO.userError "raw reference DispatchFromDyn implementation absent")
  let missingImpl := {document with definitions := document.definitions.map fun definition =>
    if definition.crateIndex == referenceImpl.definition.crateIndex && definition.index == referenceImpl.definition.index then
      {definition with sourceEnvironment := none} else definition}
  reject missingImpl source.definition "raw source environment declaration is absent"
  let missingLang := {document with traitProgram := {document.traitProgram with
    traits := document.traitProgram.traits.filter (·.definition != dispatch.definition)}}
  reject missingLang source.definition "dyn method required source lang item absent: dispatch_from_dyn"
  IO.println "PASS 10 actual source dyn declarations: 5 own entries in source order, World provider, raw receiver impl evidence and missing/malformed controls"
