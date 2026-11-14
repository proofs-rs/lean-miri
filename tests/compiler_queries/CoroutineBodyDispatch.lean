import Miri.Input.CoroutineBodyDispatch


open Miri.Input.CoroutineBodyDispatch
open Miri.Input.GenericSubstitution

def main : IO Unit := do
  let owner : DefinitionIdentity := ⟨7,11⟩
  let moved : DefinitionIdentity := ⟨7,12⟩
  let kinds := #[Kind.regular, .fnShared, .fnMut, .fnOnce]
  let mut checks := 0
  for identity in kinds do
    for requested in kinds do
      for family in #[Family.ordinary, .asyncDrop] do
        for byMove in #[none, some owner, some moved] do
          let actual := select ⟨owner,identity,byMove,family⟩ requested
          let expected : Option DefinitionIdentity :=
            if family == .asyncDrop then none
            else if requested == .regular || requested == identity then some owner
            else if requested == .fnOnce &&
                (identity == .fnShared || identity == .fnMut) && byMove == some moved then
              some moved
            else none
          unless actual.toOption == expected do
            throw (IO.userError s!"dispatch mismatch: {repr identity} {repr requested}")
          checks := checks + 1
  IO.println s!"PASS {checks} finite dispatch cases; no physical layout claims"
