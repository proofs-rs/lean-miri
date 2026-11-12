import Miri.Input.SourceMirCall

/-! Mechanism control: all source-call callbacks retain one execution-owned
world. Actual compiler identity correspondence is tested by SourceCall.lean. -/
open Miri.Input Miri.Input.GenericSubstitution

private def liftPure (value : Except String α) : TypeArena.WorldM α :=
  match value with | .ok value => pure value | .error error => throw error

private def resolve (callee : MirDirectCall.Callee) : TypeArena.WorldM SourceCall.Resolution :=
  SourceCall.resolveCalleeWith
    (fun identity => do liftPure ((← get).definitionRef identity))
    (GenericInstantiationWorld.resolveType 128)
    (fun definition arguments => do
      unless definition == 0 do throw "source definition changed"
      let #[.Type argument] := arguments | throw "source arguments changed"
      let .constructed (.integer false .u32) ← liftPure ((← get).lookupType argument)
        | throw "argument effect was discarded before instance resolution"
      pure 17) callee

private def checked : Except String Unit := do
  let initial ← TypeArena.World.ofMaterial #[] #[] #[{crateIndex := 7,index := 11}] 8
  let callee : MirDirectCall.Callee := ⟨⟨7,11⟩,#[.atom .type "uint" "u32"]⟩
  let (first,retained) ← (resolve callee).run initial
  unless first.instanceId == 17 && first.arguments == #[.Type 0] && first.functionType == 1 do
    throw "source-call identity allocation order changed"
  match initial.lookupType first.functionType with
  | .ok _ => throw "source-call construction mutated the initial world"
  | .error _ => pure ()
  let .constructed (.functionDefinition identity arguments variables) ← retained.lookupType first.functionType
    | throw "new source-call function type was not retained"
  unless identity == callee.definition && arguments == first.arguments && variables.isEmpty do
    throw "source-call constructor identity changed"
  let (again,reused) ← (resolve callee).run retained
  unless again.functionType == first.functionType && reused.typeCount == retained.typeCount do
    throw "repeated source-call resolution duplicated constructor identities"
  match (resolve {callee with arguments := #[.atom .region "erased" ""]}).run retained with
  | .ok _ => throw "non-type argument was silently discarded"
  | .error _ => pure ()

def main : IO Unit := do
  match checked with
  | .ok () => IO.println "PASS source-call callbacks retain and reuse one execution-owned world"
  | .error error => throw (IO.userError error)
