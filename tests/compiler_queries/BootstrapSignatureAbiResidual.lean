import Miri.Input.Decoder
import Miri.Input.CompilerSignatureAbi
open Miri.Input
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected compiler-selected main bootstrap export")
 let source := (← must (decodeJson (← IO.FS.readFile path))).document
 let prepared ← must (CompilerProviders.prepare (← must (lowerProgram source)))
 let world ← must ((RuntimeArrayTypes.create prepared.runtime).mapError reprStr)
 let some main := source.queries.main.entries.find? (·.signature.compilerSelectedEntry)
   | throw (IO.userError "compiler-selected main absent")
 let (argv,world) ← must ((RuntimeArrayTypes.liftType do
   let inner ← TypeArena.World.internType (.rawPointer source.queries.primitives.u8 .Not)
   TypeArena.World.internType (.rawPointer inner .Not)).run world)
 let request : Miri.Interpreter.FunctionCalls.SignatureRequest Miri.ABI.ExternAbi :=
   ⟨#[main.signature.functionPointerType,source.queries.primitives.isize,argv,source.queries.primitives.u8],
     source.queries.primitives.isize,.Rust,.Safe,false,false⟩
 if ((WorldSignatureAbi.query request).run world).isOk then
   throw (IO.userError "bootstrap nested dyn unexpectedly escaped source capability boundary")
 let expected ← must (CompilerSignatureAbi.queryWithIndex prepared.runtime prepared.signatureAbiIndex request)
 let (actual,_) ← must ((CompilerSignatureAbi.queryInWorld prepared request).run world)
 unless actual == expected do throw (IO.userError "production bootstrap fallback differs from complete compiler FnAbi")
 let noCatalog := {prepared with signatureAbiIndex := CompilerQueryIndices.signatureAbi #[]}
 if ((CompilerSignatureAbi.queryInWorld noCatalog request).run world).isOk then
   throw (IO.userError "unsupported bootstrap helper fabricated an ABI without exact material residual")
 IO.println "PASS compiler-selected main nested-dyn bootstrap production helper exact residual; missing catalog rejected"
