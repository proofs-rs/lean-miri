import Miri.Input.JsonTraversalCache

open Lean Miri.Input
private def parse (text : String) : IO Json :=
  match Json.parse text with | .ok value => pure value | .error e => throw (IO.userError e)
private def good (text expected : String) : IO Unit := do
  let (resolved,node) ← match JsonTraversalCache.resolve (← parse text) with
    | .ok value => pure value | .error e => throw (IO.userError e)
  unless resolved.root == (← parse expected) && node.audit do
    throw (IO.userError "prepared graph mismatch")
private def bad (text : String) : IO Unit := do
  if (JsonTraversalCache.resolve (← parse text)).isOk then
    throw (IO.userError "malformed prepared graph accepted")
def main : IO Unit := do
  good "{\"schema\":\"lean-miri-prepared-image\",\"schema_version\":1,\"fields\":[\"left\",\"right\"],\"nodes\":[[3,17],[5,[0,0]],[6,[[0,1],[1,1]]]],\"root\":2}"
    "{\"left\":[17,17],\"right\":[17,17]}"
  for rows in ["[[5,[0]]]", "[[7]]", "[[3,true]]", "[[0,1]]", "[[3,17],[6,[[0,0],[0,0]]]]", "[[6,[[2,0]]]]"] do
    bad s!"\{\"schema\":\"lean-miri-prepared-image\",\"schema_version\":1,\"fields\":[\"x\"],\"nodes\":{rows},\"root\":0}"
  bad "{\"schema\":\"lean-miri-prepared-image\",\"schema_version\":1,\"fields\":[\"x\",\"x\"],\"nodes\":[[6,[]]],\"root\":0}"
  bad "{\"schema\":\"lean-miri-prepared-image\",\"schema_version\":1,\"fields\":[],\"nodes\":[[6,[]]],\"root\":1}"
  IO.println "prepared image: reconstruction, aliases, bounds and malformed rows PASS"
