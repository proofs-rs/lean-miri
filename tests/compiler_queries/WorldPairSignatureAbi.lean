import Miri.Input.Decoder
import Miri.Input.CompilerSignatureAbi

open Miri.Input Miri.ABI
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameArg (aWorld bWorld : TypeArena.World) (a b : ArgAbi TypeId) : Except String Bool := do
 pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
   (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) &&
   a.layout.layout == b.layout.layout && a.mode == b.mode)
def main (args : List String) : IO Unit := do
 let [candidatePath,oraclePath] := args | throw (IO.userError "expected source candidate and actual helper oracle")
 let source := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
 let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
 unless source.queries.functionFacts.helperSignatures.isEmpty do
   throw (IO.userError "covered helper fixture retains eager dummy-signature ABI results")
 let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
 let oracleRuntime ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
 let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let oracleWorld ← must ((RuntimeArrayTypes.create oracleRuntime).mapError reprStr)
 let metadata := {runtime with source := {runtime.source with functionAbis := #[],queries := {runtime.source.queries with
   functionFacts := {runtime.source.queries.functionFacts with helperSignatures := #[], pointerAbis := #[], types := #[]}}},checkedMaterial := none}
 let world := {initial with metadata}
 let mut checked := 0
 for row in oracle.queries.functionFacts.helperSignatures do
  let inputs ← must (row.signature.inputs.mapM (GenericInstantiationWorld.ofType oracleWorld.arena 16384))
  let output ← must (GenericInstantiationWorld.ofType oracleWorld.arena 16384 row.signature.output)
  let (actual,after) ← must ((do
    let inputs ← inputs.mapM fun term => RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 term)
    let output ← RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 output)
    WorldSignatureAbi.query ⟨inputs,output,row.signature.abi,row.signature.safety,row.signature.cVariadic,row.splatted⟩).run world)
  let expected ← must (CallResolution.functionAbiId oracleRuntime row.abiId)
  unless actual.args.size == expected.args.size && actual.fixedCount == expected.fixedCount &&
    actual.cVariadic == expected.cVariadic && actual.conv == expected.conv && actual.canUnwind == expected.canUnwind &&
    (← must (sameArg after.arena oracleWorld.arena actual.ret expected.ret)) do
    throw (IO.userError "source helper ABI interface/return differs from actual rustc")
  for (a,b) in actual.args.zip expected.args do
   unless ← must (sameArg after.arena oracleWorld.arena a b) do
    throw (IO.userError "source helper ABI argument differs from actual rustc")
  checked := checked+1
 unless checked >= 8 && checked == oracle.queries.functionFacts.helperSignatures.size do throw (IO.userError s!"only {checked} helper ABI oracle cases")
 IO.println s!"PASS {checked} complete source helper ABIs, all eager helper rows and all result/signature catalogs removed"
