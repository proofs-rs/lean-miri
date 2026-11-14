import Miri.Input.Decoder
import Miri.Input.SourceCall

/-! Source identity resolution compared to real compiler call-site evidence.
The evidence is an oracle here; SourceCall does not consume it. -/
open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current source-call fixture input")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let context ← must (GenericInstantiation.Context.ofDocument document)
  let mut count := 0
  for seed in document.bodies do
    let .material body := seed | continue
    for (block,index) in body.mir.basicBlocks.zipIdx do
      let .Call (.Constant constant) .. := block.terminator.kind | continue
      let .Val .ZeroSized functionType := constant.value | continue
      let some evidence := (body.callEvidence[index]?).join | continue
      let some expectedInstance := evidence.instanceId | continue
      let some instanceNode := document.instances[expectedInstance]? | continue
      let .Item _ := instanceNode.instanceKind | continue
      let raw ← must (GenericInstantiation.ofType context 16384 functionType)
      let callee ← must (SourceCall.calleeOfFunctionTerm raw)
      let actual ← must (SourceCall.resolveCallee document 16384 callee)
      check (actual.instanceId == expectedInstance && actual.functionType == functionType)
        "ordinary source resolution disagrees with actual rustc call evidence"
      check (actual.arguments == instanceNode.genericArgs) "source generic arguments changed"
      let duplicate := {document with instances := document.instances.push instanceNode}
      match SourceCall.resolveCallee duplicate 16384 callee with
      | .ok _ => throw (IO.userError "duplicate exact Item candidate accepted")
      | .error _ => pure ()
      let retained := document.instances.filter (fun candidate => candidate.id != expectedInstance)
      let missing := {document with instances := retained}
      match SourceCall.resolveCallee missing 16384 callee with
      | .ok _ => throw (IO.userError "absent exact Item candidate accepted")
      | .error _ => pure ()
      count := count + 1
  check (count > 0) "fixture contained no ordinary source-call comparisons"
  IO.println s!"PASS {count} exact ordinary source-call identities and missing/duplicate controls"
