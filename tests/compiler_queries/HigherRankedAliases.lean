import Miri.Input.Decoder
import Miri.Input.AliasRuntime

open Lean Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def run (context : AliasRuntime.Context) (clause : Clause) : Except String Outcome :=
  fulfill context.traits (AliasRuntime.traitHooks context 1024 fun universeIndex remaining active term =>
    AliasRuntime.normalizeTermScoped context universeIndex 100000 remaining #[] active term)
    {eraseRegions := true} 1024 100000 #[clause]

private def hasAlias : Nat → GenericSubstitution.Term → Except String Bool
  | 0,_ => throw "alias oracle term inspection exhausted"
  | fuel + 1,term => do
    match term with
    | .definition _ tag _ children =>
      if tag.startsWith "alias_" then return true
      children.anyM (hasAlias fuel)
    | .node _ _ _ children => children.anyM (hasAlias fuel)
    | .binder _ body => hasAlias fuel body
    | _ => pure false

private def firstAlias : Nat → GenericSubstitution.Term → Except String (Option DefinitionIdentity)
  | 0,_ => throw "alias owner inspection exhausted"
  | fuel + 1,term => do
    let scan (children : Terms) : Except String (Option DefinitionIdentity) := do
      for child in AliasNormalization.termsToArray children do
        if let some found ← firstAlias fuel child then return some found
      pure none
    match term with
    | .definition _ tag identity children =>
      if tag.startsWith "alias_" then pure (some identity) else scan children
    | .node _ _ _ children => scan children
    | .binder _ body => firstAlias fuel body
    | _ => pure none

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh source and scoped-alias oracle")
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let context ← must (AliasRuntime.Context.ofDocument document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 7 do throw (IO.userError "incomplete scoped-alias oracle")
  let mut positive := 0
  let mut negative := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let expected ← must ((← must (row.getObjVal? "accepted")).getBool?)
    let clause ← must (Codec.readClause (← must (row.getObjVal? "goal")))
    let .trait goal := clause.predicate | throw (IO.userError "scoped-alias source goal is not a trait")
    unless ← must ((Terms.ofArray goal.traitRef.arguments).anyM (hasAlias 16384)) do
      throw (IO.userError "compiler oracle normalized away the source alias")
    match expected, ← must (run context clause) with
    | true,.proven _ => positive := positive + 1
    | false,.noSolution => negative := negative + 1
    | _,actual => throw (IO.userError s!"scoped alias trait result differs from rustc: {name}: {reprStr actual}")
    if name == "checked" then
      let mut foundOwner := none
      for argument in goal.traitRef.arguments do
        if foundOwner.isNone then foundOwner := ← must (firstAlias 16384 argument)
      let some owner := foundOwner | throw (IO.userError "checked alias physical owner absent")
      let missing := {document with definitions := document.definitions.map fun source =>
        if source.crateIndex == owner.crateIndex && source.index == owner.index then
          {source with sourceEnvironment := none} else source}
      let missingContext ← must (AliasRuntime.Context.ofDocument missing)
      match run missingContext clause with
      | .ok _ => throw (IO.userError "scoped checked alias succeeded without its canonical own clauses")
      | .error error =>
        unless error == "raw source environment declaration is absent" do
          throw (IO.userError s!"unexpected missing alias scope failure: {error}")
      let pollutedClause := {document with definitions := document.definitions.map fun source =>
        if source.crateIndex == owner.crateIndex && source.index == owner.index then
          {source with sourceEnvironment := source.sourceEnvironment.map fun material =>
            {material with ownPredicates := #[⟨#[], .equal
              (.placeholder .type 1 0 .anonymous) (.placeholder .type 1 0 .anonymous)⟩]}}
        else source}
      let pollutedContext ← must (AliasRuntime.Context.ofDocument pollutedClause)
      match run pollutedContext clause with
      | .ok _ => throw (IO.userError "raw own clause imported a live query placeholder")
      | .error error =>
        unless error == "placeholder forbidden for this generic syntax role" do
          throw (IO.userError s!"unexpected raw clause placeholder rejection: {error}")
      let polluted := {document with definitions := document.definitions.map fun source =>
        if source.crateIndex == owner.crateIndex && source.index == owner.index then
          {source with genericTemplate := source.genericTemplate.map fun template =>
            {template with typeExpression := .placeholder .type 1 0 .anonymous}}
        else source}
      match AliasRuntime.Context.ofDocument polluted with
      | .ok _ => throw (IO.userError "raw alias material imported a live query placeholder")
      | .error error =>
        unless error == "placeholder forbidden for this generic syntax role" do
          throw (IO.userError s!"unexpected material placeholder rejection: {error}")
  unless positive == 5 && negative == 2 do throw (IO.userError "scoped-alias polarity coverage changed")
  IO.println "PASS seven genuine alias-bearing quantified trait goals, including nested forall obligations and function binders"
