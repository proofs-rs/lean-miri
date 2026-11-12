import Miri.Input.Decoder
import Miri.Input.SourceMir
import Miri.Input.TypeArena

/-! The caller contains no array type. Resolving a source MIR local must create
the exact nominal-element array identity, rather than reuse a layout match. -/
open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh novel-array input")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let some index := document.bodies.findIdx? (fun seed => match seed with
    | .copyTemplate reference => match document.mirTemplates[reference.templateId]? with
      | some source => source.defPath.endsWith "local_array"
      | none => false
    | _ => false) | throw (IO.userError "local_array was not exported as a source template")
  let body ← must (SourceMir.resolveBody document index)
  let some result := body.mir.locals[0]? | throw (IO.userError "missing return local")
  let some novelArray := body.mir.locals.find? (fun declaration => declaration >= document.types.size)
    | throw (IO.userError "template did not construct an absent material type")
  let node ← must (TypeArena.node document.types novelArray document.typeConstants.size)
  match node.shape with
  | .array element _ constructor =>
    check (element == result && constructor.count == 2)
      "constructed array has the wrong nominal element or length"
    check (!(document.types.any fun node => match node.shape with
      | .array ty _ length => ty == element && length.count == 2
      | _ => false)) "concrete array was already present in material seeds"
  | _ => throw (IO.userError "new local type is not an array")
  IO.println "PASS on-demand MIR local creates absent nominal-element array type"
