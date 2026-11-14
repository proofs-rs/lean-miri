import Miri.Input.TraitSelection.HigherRankedMatch
import Miri.Input.TraitSelection.Codec

/-! Finite head-relation comparisons. The independent oracle also fulfills the
complete fixture obligations; the fixture impls have no explicit where clauses.
This does not turn the head matcher into a trait fulfillment provider. -/
open Lean Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [oraclePath] := args | throw (IO.userError "expected pinned quantified obligation oracle")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 8 do throw (IO.userError "incomplete quantified obligation oracle")
  let mut positives := 0
  let mut negatives := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let expected ← must ((← must (row.getObjVal? "accepted")).getBool?)
    let rawImpl ← must (row.getObjVal? "implementation")
    let definition ← must (GenericMaterialCodec.readDefinition (← must (rawImpl.getObjVal? "definition")))
    let parameters ← (← must ((← must (rawImpl.getObjVal? "parameters")).getArr?)).mapM fun value =>
      must (GenericMaterialCodec.readSort value)
    let traitRef ← must (Codec.readTraitRef (← must (rawImpl.getObjVal? "trait_ref")))
    let implementation : Impl := {
      definition := definition
      parameters := parameters
      traitRef := traitRef
      polarity := .positive
      isDefault := false
      associatedValues := #[]}
    let clause ← must (Codec.readClause (← must (row.getObjVal? "goal")))
    let actual ← must (HigherRankedMatch.headClause 1024 implementation clause)
    unless actual.isSome == expected do
      throw (IO.userError s!"quantified head relation disagrees with rustc obligation: {name}")
    -- Free-region erasure must not erase a forall placeholder or turn a
    -- static-only implementation into a higher-ranked implementation.
    let erased ← must (HigherRankedMatch.headClause 1024 implementation clause true)
    unless erased.isSome == expected do
      throw (IO.userError s!"region-erasing query lost quantified ownership: {name}")
    if expected then positives := positives + 1 else negatives := negatives + 1
  unless positives == 4 && negatives == 4 do throw (IO.userError "quantified oracle polarity coverage changed")
  IO.println "PASS eight pinned quantified obligation/head comparisons, including forall/static and repeated-region negatives"
