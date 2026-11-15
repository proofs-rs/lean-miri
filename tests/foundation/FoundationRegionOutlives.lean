import Miri.Frontend.FoundationSourceMaterial
import Miri.Input.SourceAbi
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def rejects (value : Except String A) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported outlives relation accepted")
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine region predicate source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let source ← IO.ofExcept (typedSourceMaterial document)
  let [declaration] := (source.declarations.filter (·.path == "reflexive")).toList
    | throw (IO.userError "reflexive declaration absent")
  let some abi := source.abi | throw (IO.userError "typed predicates absent")
  let [owner] := (abi.owners.filter (·.owner == declaration.definition)).toList
    | throw (IO.userError "predicate owner absent")
  let [pair] := (owner.clauses.filterMap fun clause => match clause with
    | .regionOutlives longer shorter => some (longer,shorter) | _ => none).toList
    | throw (IO.userError "actual region predicate not retained")
  unless pair == (.earlyParameter 0,.earlyParameter 0) do throw (IO.userError "early region identity changed")
  let _ ← IO.ofExcept (SourceAbi.checkRegionOutlives source owner.owner pair.1 pair.2)
  let _ ← IO.ofExcept (SourceAbi.checkRegionOutlives source owner.owner .static .static)
  for (longer,shorter) in #[(.earlyParameter 0,.static),(.earlyParameter 1,.earlyParameter 1),
      (.earlyParameter 99,.earlyParameter 99),(.erased,.erased),(.bound 0 0 .anonymous,.bound 0 0 .anonymous)] do
    rejects (SourceAbi.checkRegionOutlives source owner.owner longer shorter)
  let [typeDecl] := (source.declarations.filter (·.path == "type_outlives")).toList
    | throw (IO.userError "type outlives declaration absent")
  let [typeOwner] := (abi.owners.filter (·.owner == typeDecl.definition)).toList
    | throw (IO.userError "type outlives owner absent")
  let [typeRef] := (typeOwner.clauses.filterMap fun clause => match clause with
    | .typeOutlives type (.earlyParameter 0) => some type | _ => none).toList
    | throw (IO.userError "actual T:'a clause not retained")
  let some physical := source.physical | throw (IO.userError "source types absent")
  match ← IO.ofExcept (SourceTypes.instantiate physical #[none,some (.primitive "uint" "u8")]
      #[none,none] typeRef) with
  | .primitive "uint" "u8" => pure ()
  | _ => throw (IO.userError "type outlives T slot differs")
  rejects (SourceTypes.instantiate physical #[none,none] #[none,none] typeRef)
  let _ ← IO.ofExcept (SourceAbi.checkRegionOutlives source typeOwner.owner (.earlyParameter 0) (.earlyParameter 0))
  IO.println "genuine early-region and T:'a source identities retained; unsupported regions and missing T reject"
