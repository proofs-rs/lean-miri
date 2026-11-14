import Miri.Input.WorldNormalization
open Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def context : AliasRuntime.Context := {
  generic := {types := #[],definitions := #[],constants := #[],pointerBytes := 8},
  aliases := {freeRules := #[],associatedDeclarations := #[]}, traits := {traits := #[]} }
def main : IO Unit := do
  let initial ← must (World.ofMaterial #[] #[] #[] #[] 8)
  let (root,world) ← must ((do
    let mut id ← World.internType .bool
    for _ in [:64] do id ← World.internType (.tuple #[id,id])
    pure id : WorldM TypeId).run initial)
  let (normalized,after) ← must ((WorldNormalization.normalizeType context 10000 256 root).run world)
  unless normalized == root && after.typeCount == world.typeCount do
    throw (IO.userError "normalization changed closed shared tuple DAG identity")
  -- A second execution deliberately reuses the first execution's root number
  -- for different syntax which must normalize to a newly interned reference.
  let (otherRoot,other) ← must ((do
    let mut id ← World.internType .bool
    for _ in [:63] do id ← World.internType (.tuple #[id,id])
    World.internType (.reference 0 .Mut .Static) : WorldM TypeId).run initial)
  unless otherRoot == root do throw (IO.userError "cross-execution collision control missing")
  let (otherNormalized,otherAfter) ← must ((WorldNormalization.normalizeType context 10000 256 otherRoot).run other)
  unless otherNormalized != otherRoot && otherAfter.typeCount == other.typeCount + 1 do
    throw (IO.userError "normalization reused a result from another execution")
  match ← must (otherAfter.lookupType otherNormalized) with
  | .constructed (.reference 0 .Mut .Erased) => pure ()
  | _ => throw (IO.userError "reference normalization did not retain new canonical syntax")
  IO.println "PASS 64-level shared World DAG normalization and independent-execution identity collision control"
