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
 let [path] := args | throw (IO.userError "expected foreign FnPtr residual fixture")
 let source := (← must (decodeJson (← IO.FS.readFile path))).document
 let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
 let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let prepared ← must (CompilerFunctionFacts.prepare runtime (← must (lowerProgram source)))
 let rows := source.queries.functionFacts.pointerAbis.filter fun row =>
   (source.types[row.typeId]?).any fun node => match node.shape with
   | .functionPointer signature _ => signature.abi == .C false
   | _ => false
 let #[row] := rows | throw (IO.userError "missing unique foreign ABI residual")
 if ((WorldFunctionPointerAbi.construct row.typeId #[]).run world).isOk then
   throw (IO.userError "foreign FnPtr escaped raw Rust calling-convention boundary")
 let expected ← must (CallResolution.functionAbiId runtime row.abiId)
 let (actual,after) ← must ((CompilerFunctionFacts.pointerAbiInWorld prepared row.typeId #[]).run world)
 unless actual.args.size == expected.args.size && actual.conv == expected.conv && actual.cVariadic == expected.cVariadic &&
   actual.fixedCount == expected.fixedCount && actual.canUnwind == expected.canUnwind &&
   (← must (sameArgument after.arena world.arena actual.ret expected.ret)) do
   throw (IO.userError "foreign FnPtr exact residual differs from actual compiler ABI")
 for (a,b) in actual.args.zip expected.args do
   unless ← must (sameArgument after.arena world.arena a b) do throw (IO.userError "foreign FnPtr residual argument differs")
 let (novel,extended) ← must ((RuntimeArrayTypes.liftType (TypeArena.World.internType (.functionPointer {
   abiPacked := Miri.ABI.ExternAbi.asPacked (.C false),safe := true,cVariadic := false,splatted := none,
   inputs := #[source.queries.primitives.u16],output := source.queries.primitives.u8 }))).run world)
 unless novel >= world.arena.typeCount do throw (IO.userError "foreign negative key was not constructed")
 let forged := {prepared with pointerAbis := prepared.pointerAbis.push ⟨novel,#[],.ok row.abiId⟩}
 if ((CompilerFunctionFacts.pointerAbiInWorld forged novel #[]).run extended).isOk then
   throw (IO.userError "constructed foreign FnPtr borrowed injected numeric material residual")
 IO.println "PASS foreign FnPtr exact material residual, constructed unsupported key and injected numeric row rejected"
