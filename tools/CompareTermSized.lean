import Miri.Input.Decoder
import Miri.Input.AliasRuntime
import Miri.Input.TermSized
open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [source,oracle] := args | throw (IO.userError "expected source.json oracle.json")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let context ← must (AliasRuntime.Context.ofDocument decoded.document)
  let hooks := AliasRuntime.sizedHooks context
    (fun fuel term => AliasRuntime.normalizeTerm context 10000 fuel #[] #[] term)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oracle))).getArr?)
  let mut queries := 0
  let mut novel := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    match GenericInstantiation.resolveType context.generic 256 term with
    | .error _ => novel := novel + 1
    | .ok _ => pure ()
    for (kind,langItem,key) in #[(StructuralSized.TraitKind.sized,"sized","is_sized"),(.metaSized,"meta_sized","is_meta_sized")] do
      let expected ← must ((← must (row.getObjVal? key)).getBool?)
      let actual ← must (TermSized.query hooks kind 256 term)
      check (actual == expected) s!"term {key} differs from independent pinned rustc"
      let declarations := context.traits.traits.filter (·.langItem == some langItem)
      check (declarations.size == 1) s!"fixture must capture exactly one {langItem} declaration"
      let some declaration := declarations[0]? | throw (IO.userError "sizedness trait declaration absent")
      let outcome ← must (AliasRuntime.solveGoal context 256 10000 ⟨.positive,⟨declaration.definition,#[term]⟩⟩)
      match outcome with
      | .proven _ => check expected s!"production {langItem} incorrectly proved unsized term"
      | .noSolution => check (!expected) s!"production {langItem} incorrectly rejected sized term"
      | .ambiguous reason => throw (IO.userError s!"unexpected {langItem} ambiguity: {reason}")
      if let .definition .type "adt" .. := term then
        let missing := {context with generic := {context.generic with
          definitions := context.generic.definitions.map fun definition =>
            {definition with adtDeclaration := none}}}
        match AliasRuntime.solveGoal missing 256 10000 ⟨.positive,⟨declaration.definition,#[term]⟩⟩ with
        | .ok _ => throw (IO.userError "missing canonical ADT declaration produced a trait answer")
        | .error error =>
          check (error == "term Sized canonical ADT declaration absent")
            s!"missing ADT declaration control failed for unrelated reason: {error}"
      queries := queries + 1
  check (novel >= 4) "fixture did not exercise novel type expressions absent from material TypeIds"
  IO.println s!"PASS {queries} raw-term Sized/MetaSized answers equal independent rustc, including {novel} novel type expressions and actual trait provider dispatch"
