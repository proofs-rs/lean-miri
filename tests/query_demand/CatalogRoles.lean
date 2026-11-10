import Miri.Input
import Miri.Input.CompilerNativeSignatures
import Miri.Input.CompilerThreadLocal

/-! Finite decoder/provider checks on mutations of fresh compiler exports.
Manifest cases retain separate baselines, readiness and demanded query
failures. This does not execute MIR or certify completeness of query roles. -/
open Lean Miri.Input Miri.Interpreter
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def read (dir file : String) : IO ExecutionInput := do
  must (decodeJson (← IO.FS.readFile (dir ++ "/" ++ file)))
private def arr (value : Json) (key : String) : Except String (Array Json) :=
  (value.getObjVal? key).bind Json.getArr?
private def getAt (values : Array A) (index : Nat) : Except String A :=
  match values[index]? with | some value => pure value | none => .error "manifest query row absent"

def main (args : List String) : IO Unit := do
  let some dir := args.head? | throw (IO.userError "fresh-export case manifest directory required")
  let manifest ← must (Json.parse (← IO.FS.readFile (dir ++ "/cases.json")))
  let mut count := 0
  for row in ← must (arr manifest "cases") do
    let name ← must (row.getObjValAs? String "file")
    let source ← IO.FS.readFile (dir ++ "/" ++ name)
    let ready ← must (row.getObjValAs? Bool "ready")
    let full := decodeJson source
    check (full.isOk == ready) s!"decoder readiness differs: {name}"
    if ready then
      let provider ← must (row.getObjValAs? String "provider")
      unless provider == "none" do
        let baseline ← read dir (← must (row.getObjValAs? String "baseline"))
        let decoded ← must full
        let program ← must (lowerProgram baseline.document)
        let prepared ← must (CompilerProviders.prepare program)
        let mutated ← must (CompilerProviders.prepare (← must (lowerProgram decoded.document)))
        match provider with
        | "native" =>
          let entry ← must (getAt baseline.document.queries.nativeSignatures (← must (row.getObjValAs? Nat "index")))
          let callee := entry.instanceId
          discard <| must (CompilerNativeSignatures.query prepared callee)
          let invalidId := prepared.program.input.instances.size
          let queries := prepared.program.input.queries
          let invalidQueries := {queries with nativeSignatures := #[{entry with instanceId := invalidId}]}
          let invalidProgram := {prepared.program with input := {prepared.program.input with queries := invalidQueries}}
          let invalid := {prepared with program := invalidProgram}
          check (!(CompilerNativeSignatures.query invalid invalidId).isOk)
            "native query accepted out-of-bounds full-instance identity"
          discard <| must (CompilerNativeSignatures.query mutated callee)
        | "tls" =>
          let definition ← must (row.getObjValAs? Nat "definition")
          discard <| must (CompilerThreadLocal.forDefinition prepared.program definition)
          discard <| must (CompilerThreadLocal.forDefinition mutated.program definition)
        | provider => throw (IO.userError s!"unknown demand provider: {provider}")
    count := count + 1
  IO.println s!"catalog cases: {count} checked at decoder and demanded-provider boundaries; no MIR equivalence claim"
