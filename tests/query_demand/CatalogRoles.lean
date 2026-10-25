import Miri.Input
import Miri.Input.CompilerNativeSignatures
import Miri.Input.CompilerThreadLocal

/-! Finite decoder/provider checks on mutations of fresh compiler exports.
Manifest cases retain separate baselines, exact obligations and demanded query
failures. This does not execute MIR or certify completeness of query roles. -/
open Lean Miri.Input Miri.Interpreter
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def read (dir file : String) : IO DecodeResult := do
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
    let baseline ← read dir (← must (row.getObjValAs? String "baseline"))
    let decoded ← read dir name
    let expected ← must (row.getObjValAs? Bool "ready")
    check (baseline.executionInput.isSome) s!"fresh compiler baseline not structurally ready: {name}"
    check (decoded.executionInput.isSome == expected) s!"query role readiness mismatch: {name}"
    for issue in baseline.document.obligations do
      check (decoded.document.obligations.any fun actual => actual.path == issue.path && actual.message == issue.message)
        s!"baseline obligation erased in {name}: {issue.path}"
    check (decoded.document.obligations.size > baseline.document.obligations.size)
      s!"mutated unsupported evidence disappeared: {name}"
    let provider ← must (row.getObjValAs? String "provider")
    if provider != "none" then
      let program ← must (lowerProgram decoded.document)
      let p ← must (CompilerProviders.prepare program)
      let index ← must (row.getObjValAs? Nat "index")
      let unavailable ← match provider with
        | "native" => do
          let entry ← must (getAt (← must (arr program.input.raw "compiler_native_signature_queries")) index)
          let (callee,_) ← must (CompilerInstance.decode (LowerContext.ofDocument program.input) program.compilerTables entry)
          pure (!(CompilerNativeSignatures.query p callee).isOk)
        | _ => throw (IO.userError s!"unknown provider case: {provider}")
      check unavailable s!"demanded missing provider silently succeeded: {name}"
    count := count + 1
  IO.println s!"catalog demand roles: {count} finite readiness/obligation/provider cases passed; no MIR equivalence claim"
