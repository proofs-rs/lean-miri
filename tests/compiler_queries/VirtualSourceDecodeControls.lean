import Miri.Input.Decoder

def main (args : List String) : IO Unit := do
  let [positive,item,identity,shim] := args | throw (IO.userError "expected Virtual source and three malformed source controls")
  match Miri.Input.decodeJson (← IO.FS.readFile positive) with
  | .error error => throw (IO.userError s!"valid source Virtual document rejected: {error}")
  | .ok _ => pure ()
  for (path,expected) in #[(item,"symbol identity that has no imported MIR body"),
      (identity,"source Virtual FnDef differs from its complete canonical instance"),
      (shim,"raw source ABI requires an Item or Virtual instance")] do
    match Miri.Input.decodeJson (← IO.FS.readFile path) with
    | .ok _ => throw (IO.userError s!"malformed source Virtual control accepted: {path}")
    | .error error => unless error.contains expected do
        throw (IO.userError s!"source control failed at an unrelated boundary: {error}")
  IO.println "PASS source Virtual rooted decoder;bodyless Item/shim and wrong physical Virtual identity rejected"
