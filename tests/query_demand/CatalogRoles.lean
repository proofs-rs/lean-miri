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
    let source ← IO.FS.readFile (dir ++ "/" ++ name)
    let ready ← must (row.getObjValAs? Bool "ready")
    let full := decodeJson source
    let runtime := decodeRuntimeJson source
    check (full.isOk == ready && runtime.isOk == ready) s!"decoder readiness differs: {name}"
    if ready then
      let decoded ← must full
      let program ← must (lowerProgram baseline.document)
      let prepared ← must (CompilerProviders.prepare program)
      let mutated ← must (CompilerProviders.prepare (← must (lowerProgram decoded.document)))
      match ← must (row.getObjValAs? String "provider") with
      | "native" =>
        let entries ← must (arr baseline.document.raw "compiler_native_signature_queries")
        let entry ← must (getAt entries (← must (row.getObjValAs? Nat "index")))
        let (callee,_) ← must (CompilerInstance.decode
          (LowerContext.ofDocument prepared.program.input) prepared.program.compilerTables entry)
        discard <| must (CompilerNativeSignatures.query prepared callee)
        check (!(CompilerNativeSignatures.query mutated callee).isOk)
          s!"demanded malformed native signature accepted: {name}"
      | "tls" =>
        let definitionJson ← must (row.getObjVal? "definition")
        let definition : DefinitionId := ⟨← must (definitionJson.getObjValAs? Nat "crate"),
          ← must (definitionJson.getObjValAs? Nat "index")⟩
        let definition ← must (lookupDefinitionId program.bundle.definitions definition)
        discard <| must (CompilerThreadLocal.forDefinition prepared.program definition)
        check (!(CompilerThreadLocal.forDefinition mutated.program definition).isOk)
          s!"demanded malformed TLS initializer accepted: {name}"
      | provider => throw (IO.userError s!"unknown demand provider: {provider}")
    else
      match full, runtime with
      | .error full, .error runtime =>
        check (full == runtime) s!"query failure diagnostics differ: {name}"
      | _, _ => throw (IO.userError s!"malformed catalog input accepted: {name}")
    count := count + 1
  IO.println s!"catalog cases: {count} checked at decoder and demanded-provider boundaries; no MIR equivalence claim"
