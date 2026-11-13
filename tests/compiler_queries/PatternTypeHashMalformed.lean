import Miri.Input.WorldTypeHash
open Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit := do
  if value.isOk then throw (IO.userError "malformed Pattern hash source accepted")
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  {id,shape,display := "raw Pattern malformed control",layoutId := 0}
def main : IO Unit := do
  let source := #[node 0 (.uint (.known .u8)),node 1 (.patternType 0 (.range 0 0))]
  let malformed : Miri.MIR.TypeConst := .Value 0 {root := 0,nodes := #[.Leaf 300 1]}
  let world ← must (World.ofMaterial source #[malformed] #[] 8)
  rejects (WorldTypeHash.sourceBytes world 4096 1)
  let world ← must (World.ofMaterial source #[] #[] 8)
  rejects ((World.internType (.patternType 0 (.range 0 0))).run world)
  let (id,world) ← must ((World.internType (.patternType 0 (.or #[]))).run world)
  rejects (WorldTypeHash.sourceBytes world 4096 id)
  let malformedTerm : Term := .node .type "pattern" "" (.cons (.atom .type "uint" "u8")
    (.cons (.node .aggregate "pattern_range" "" .nil) .nil))
  rejects ((GenericInstantiationWorld.resolveType 4096 malformedTerm).run world)
  IO.println "PASS malformed endpoint scalar, missing constant, empty Or source and malformed pattern syntax reject explicitly"
