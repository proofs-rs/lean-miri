import Miri.Input.Decoder
import Miri.Input.AliasRuntime

/-! Fresh raw-source trait catalogs and complete runtime fulfillment against an
independent rustc obligation oracle. Reaching Unsupported or ambiguity fails the
comparison; a missing declaration scope and malformed forall ownership reject. -/
open Lean Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def run (context : AliasRuntime.Context) (clause : Clause) : Except String Outcome :=
  let work := 100000
  let hooks := AliasRuntime.traitHooks context 1024 fun universeIndex remaining active term =>
    AliasRuntime.normalizeTermScoped context universeIndex work remaining #[] active term
  fulfill context.traits hooks {eraseRegions := true} 1024 work #[clause]

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh export and quantified rustc oracle")
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let context ← must (AliasRuntime.Context.ofDocument document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 8 do throw (IO.userError "incomplete runtime higher-ranked oracle")
  let mut positive := 0
  let mut negative := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let expected ← must ((← must (row.getObjVal? "accepted")).getBool?)
    let clause ← must (Codec.readClause (← must (row.getObjVal? "goal")))
    let actual ← must (run context clause)
    match expected,actual with
    | true,.proven _ => positive := positive + 1
    | false,.noSolution => negative := negative + 1
    | _,_ => throw (IO.userError s!"runtime higher-ranked selection differs from rustc: {name}: {reprStr actual}")
    if name == "all" then
      let rawImpl ← must (row.getObjVal? "implementation")
      let implementation ← must (GenericMaterialCodec.readDefinition (← must (rawImpl.getObjVal? "definition")))
      let missing := {document with definitions := document.definitions.map fun definition =>
        if definition.crateIndex == implementation.crateIndex && definition.index == implementation.index
        then {definition with sourceEnvironment := none} else definition}
      let missingContext ← must (AliasRuntime.Context.ofDocument missing)
      match run missingContext clause with
      | .ok _ => throw (IO.userError "quantified candidate succeeded without canonical source obligations")
      | .error error =>
        unless error == "raw source environment declaration is absent" do
          throw (IO.userError s!"unexpected missing quantified scope failure: {error}")
      let malformed := {clause with variables := #[.region (.namedForPrinting "wrong_owner")]}
      match run context malformed with
      | .ok _ => throw (IO.userError "quantified clause ignored its bound-region owner identity")
      | .error error =>
        unless error == "bound region identity mismatch" do
          throw (IO.userError s!"unexpected malformed quantified ownership failure: {error}")
    if name == "fn_for" then
      for variableKind in [BoundVariable.type .anonymous, BoundVariable.constant] do
        let unsupported := {clause with variables := #[variableKind]}
        match run context unsupported with
        | .ok _ => throw (IO.userError "type/constant forall gained unsupported bound assumptions")
        | .error error =>
          unless error == "quantified type/constant clauses require their bound assumptions and candidate semantics" do
            throw (IO.userError s!"unexpected unsupported quantifier failure: {error}")
  unless positive == 4 && negative == 4 do throw (IO.userError "runtime quantified polarity coverage changed")
  IO.println "PASS eight full runtime quantified trait selections against pinned rustc, with missing-source and malformed-owner rejection"
