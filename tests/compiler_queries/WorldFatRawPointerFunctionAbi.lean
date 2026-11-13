import Miri.Input.Decoder
import Miri.Input.CompilerFunctionFacts

open Miri.Input
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameArgument (aWorld bWorld : TypeArena.World) (a b : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
 pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
   (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) &&
   a.layout.layout == b.layout.layout && a.mode == b.mode)
def main (args : List String) : IO Unit := do
 let [path,oraclePath] := args | throw (IO.userError "expected candidate and actual rustc FnPtr oracle")
 let decoded := (← must (decodeJson (← IO.FS.readFile path))).document
 let document := {decoded with types := decoded.types.map (fun node =>
   {node with compilerFacts := node.compilerFacts.map (fun facts =>
     {facts with booleanQueries := #[],projectionQueries := none})})}
 let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
 let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
 let oracleRuntime ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
 let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let oracleWorld ← must ((RuntimeArrayTypes.create oracleRuntime).mapError reprStr)
 let source := {runtime.source with functionAbis := #[], queries := {runtime.source.queries with
   functionFacts := {runtime.source.queries.functionFacts with types := #[], pointerAbis := #[]}}}
 let world := {initial with metadata := {runtime with source,checkedMaterial := none}}
 let program ← must (lowerProgram source)
 let prepared ← must (CompilerFunctionFacts.prepare world.metadata program)
 let mut count := 0
 for row in oracle.queries.functionFacts.pointerAbis do
  unless row.extraArgumentTypes.isEmpty do throw (IO.userError "unexpected extra ABI arguments")
  let wanted ← must (GenericInstantiationWorld.ofType oracleWorld.arena 16384 row.typeId)
  let matching ← must (document.types.filterM fun node => do
    if node.shapeKind != .functionPointer then return false
    pure ((← GenericInstantiationWorld.ofType initial.arena 16384 node.id) == wanted))
  let #[node] := matching | throw (IO.userError "no unique matching raw FnPtr source constructor")
  if document.queries.functionFacts.pointerAbis.any (·.typeId == node.id) then
    throw (IO.userError "covered source FnPtr retains eager ABI result")
  let expected ← must (CallResolution.functionAbiId oracleRuntime row.abiId)
  let (actual,after) ← must ((CompilerFunctionFacts.pointerAbiInWorld prepared node.id #[]).run world)
  unless actual.args.size == expected.args.size && actual.conv == expected.conv &&
      actual.cVariadic == expected.cVariadic && actual.fixedCount == expected.fixedCount &&
      actual.canUnwind == expected.canUnwind && (← must (sameArgument after.arena oracleWorld.arena actual.ret expected.ret)) do
    throw (IO.userError s!"function pointer ABI interface/return mismatch type {node.id}")
  for (a,b) in actual.args.zip expected.args do
    unless ← must (sameArgument after.arena oracleWorld.arena a b) do
      throw (IO.userError s!"function pointer ABI argument mismatch type {node.id}")
  let (signature,_) ← must ((CompilerFunctionFacts.signatureInWorld prepared node.id).run world)
  let raw ← must (WorldFunctionPointerAbi.sourceSignature initial.arena node.id)
  unless signature == (raw.inputs.size,raw.abi) do throw (IO.userError "FnPtr source signature differs")
  let noSession := {world with metadata := {world.metadata with source :=
    {source with producer := {source.producer with abiSession := none}}}}
  if ((CompilerFunctionFacts.pointerAbiInWorld prepared node.id #[]).run noSession).isOk then
    throw (IO.userError "FnPtr ABI accepted missing canonical session")
  count := count+1
 unless count >= 12 && count == oracle.queries.functionFacts.pointerAbis.size do throw (IO.userError s!"only {count} source FnPtr ABI queries")
 if ((WorldFunctionPointerAbi.construct document.queries.primitives.u8 #[]).run world).isOk then
   throw (IO.userError "non-FnPtr source type accepted as FnPtr ABI")
 IO.println s!"PASS {count} production complete FnPtr ABIs with result/signature catalogs removed, missing session and wrong kind rejected"
