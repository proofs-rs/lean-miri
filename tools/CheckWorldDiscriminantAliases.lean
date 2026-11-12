import Miri.Input.Decoder
import Miri.Input.CompilerDiscriminantFacts
open Miri.Input TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected raw alias source export")
  let source := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let context ← must (CompilerFacts.ofProgram runtime (← must (lowerProgram source)))
  let world ← must (World.ofDocument source)
  let mut count := 0
  for node in source.types do
    if let .alias .free false .. := node.shape then
      let ((root,fromAlias,fromRoot,value),_) ← must ((do
        let root ← CompilerFacts.normalizeInWorld context node.id
        let fromAlias ← CompilerFacts.requiredTypeInWorld context node.id "discriminant_type"
        let fromRoot ← CompilerFacts.requiredTypeInWorld context root "discriminant_type"
        let value ← CompilerDiscriminantFacts.discriminantValue context node.id 0
        pure (root,fromAlias,fromRoot,value)).run world)
      unless root != node.id && fromAlias == fromRoot && value.isNone do
        throw (IO.userError "alias discriminant query did not inspect normalized primitive root")
      count := count + 1
  unless count > 0 do throw (IO.userError "no actual alias queries tested")
  IO.println s!"PASS {count} actual source aliases normalize before world discriminant type/value queries"
