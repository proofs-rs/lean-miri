import Miri.Input.Decoder
import Miri.Input.CompilerInstance
import Miri.Input.CompilerRuntimeQueries

open Lean Miri Miri.Input

private def must (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def value (input : Json) (key : String) : Except String Json := do
  let query ← input.getObjVal? key
  unless (← query.getObjValAs? String "status") == "supported" do throw "unavailable"
  query.getObjVal? "value"

private def compareInstance (ctx : LowerContext) (tables : MIRInputTables)
    (input : Except String Json) (id : Except String Nat) : IO Unit := do
  let expected := do CompilerInstance.decode ctx tables.compiler (← input)
  let actual := id.bind tables.instance
  match expected,actual with
  | .ok (expected,next),.ok actual =>
    unless expected == actual do throw (IO.userError "runtime query full instance changed")
    unless next = tables.compiler do throw (IO.userError "runtime query requires another interner")
  | .error _,.error _ => pure ()
  | _,_ => throw (IO.userError "runtime query instance availability changed")

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: RuntimeQueryIDs <export.json>")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let document := decoded.document
  let tables := document.mirTables
  let ctx := LowerContext.ofDocument document
  let prepared ← must (CompilerRuntimeQueries.prepare (← must (lowerCoreProgram document)))
  unless !(CompilerRuntimeQueries.mutPointerType prepared document.types.size).isOk &&
      !(CompilerRuntimeQueries.resolveDropGlue prepared document.types.size).isOk do
    throw (IO.userError "out-of-bounds runtime type query accepted")
  let raw ← must (document.raw.getObjVal? "compiler_runtime_queries")
  let types ← must (raw.getObjVal? "types" >>= Json.getArr?)
  let indexed ← must tables.runtimeTypes
  for input in types do
    let id ← must (input.getObjValAs? Nat "input_type_id")
    let some (some actual) := indexed[id]? | throw (IO.userError "runtime type ID absent")
    unless actual.pointerType == (← must ((← must (value input "mut_pointer_type")).getObjValAs? Nat "type_id")) &&
        actual.referenceType == (← must ((← must (value input "mut_reference_type")).getObjValAs? Nat "type_id")) do
      throw (IO.userError "runtime pointer/reference type changed")
    compareInstance ctx tables (value input "drop_glue") actual.dropGlue
    unless (← must (CompilerRuntimeQueries.mutPointerType prepared id)) == actual.pointerType &&
        (← must (CompilerRuntimeQueries.mutReferenceType prepared id)) == actual.referenceType do
      throw (IO.userError "runtime type array lookup changed")
  let virtuals ← must (raw.getObjVal? "virtual" >>= Json.getArr?)
  let compiled ← must tables.runtimeVirtual
  unless virtuals.size == compiled.size do throw (IO.userError "virtual query count changed")
  for (input,index) in virtuals.toList.zipIdx do
    let some actual := compiled[index]? | throw (IO.userError "virtual query absent")
    compareInstance ctx tables (input.getObjVal? "original") (.ok actual.original)
    compareInstance ctx tables (value input "resolved") actual.resolved
    let args ← must (ctx.decodeCompilerValue (← must (input.getObjVal? "rebased_args")))
    let (args,next) ← must (lowerCompilerGenericArgs ctx tables.compiler args)
    unless args == actual.rebasedArgs do throw (IO.userError "virtual rebased arguments changed")
    unless next = tables.compiler do throw (IO.userError "virtual arguments need another interner")
    for (key,id) in [("method_definition",actual.methodDefinition),("parent_trait",actual.parentTrait)] do
      let source ← must (input.getObjVal? key)
      let some target := tables.compiler.definitions[id]? | throw (IO.userError "virtual definition ID absent")
      unless target.crateIndex == (← must (source.getObjValAs? Nat "crate")) &&
          target.index == (← must (source.getObjValAs? Nat "index")) do
        throw (IO.userError "virtual definition changed")
  let native ← must (document.raw.getObjVal? "compiler_native_signature_queries" >>= Json.getArr?)
  let compiled ← must tables.nativeSignatures
  unless native.size == compiled.size do throw (IO.userError "native signature count changed")
  for (input,index) in native.toList.zipIdx do
    let some actual := compiled[index]? | throw (IO.userError "native signature absent")
    compareInstance ctx tables (.ok input) (.ok actual.instanceId)
    let expected := do
      let signature ← value input "signature_query"
      let inputs ← (← (← signature.getObjVal? "inputs").getArr?).mapM (fun (input : Json) => input.getObjValAs? Nat "type_id")
      let output ← (← signature.getObjVal? "output").getObjValAs? Nat "type_id"
      return (inputs,output)
    match expected,actual.signature with
    | .ok expected,.ok actual => unless expected == actual do throw (IO.userError "native signature changed")
    | .error _,.error _ => pure ()
    | _,_ => throw (IO.userError "native signature availability changed")
  IO.println s!"runtime query IDs: PASS ({types.size} type queries; {virtuals.size} virtual; {native.size} native signatures)"
