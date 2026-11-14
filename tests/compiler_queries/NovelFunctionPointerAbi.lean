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
 let [basePath,oraclePath] := args | throw (IO.userError "expected novel FnPtr base/oracle")
 let base := (← must (decodeJson (← IO.FS.readFile basePath))).document
 let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
 let runtime ← must ((RuntimeMetadata.ofDocument base).mapError toString)
 let oracleRuntime ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
 let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let oracleWorld ← must ((RuntimeArrayTypes.create oracleRuntime).mapError reprStr)
 let (fnptr,constructed) ← must ((RuntimeArrayTypes.liftType do
   let length ← TypeArena.World.internConstant (.Value base.queries.primitives.usize ⟨#[.Leaf 13 initial.arena.pointerBytes],0⟩)
   let array ← TypeArena.World.internType (.array base.queries.primitives.u8 length)
   let reference ← TypeArena.World.internType (.reference array .Mut .Erased)
   let fnptr ← TypeArena.World.internType (.functionPointer {
     abiPacked := Miri.ABI.ExternAbi.asPacked .Rust,safe := true,cVariadic := false,splatted := none,
     inputs := #[reference],output := reference })
   unless array >= initial.arena.typeCount && reference >= initial.arena.typeCount && fnptr >= initial.arena.typeCount do
     throw "novel FnPtr chain borrowed source type IDs"
   pure fnptr).run initial)
 let source := {runtime.source with functionAbis := #[],queries := {runtime.source.queries with
   functionFacts := {runtime.source.queries.functionFacts with pointerAbis := #[]}}}
 let world := {constructed with metadata := {runtime with source,checkedMaterial := none}}
 let prepared ← must (CompilerFunctionFacts.prepare world.metadata (← must (lowerProgram source)))
 let (kind,_) ← must ((CompilerFunctionFacts.kindInWorld prepared fnptr).run world.arena)
 let .FnPtr := kind | throw (IO.userError "novel FnPtr constructor lost its function kind")
 let (_,_) ← must ((CompilerFunctionFacts.signatureInWorld prepared fnptr).run world)
 let (actual,after) ← must ((CompilerFunctionFacts.pointerAbiInWorld prepared fnptr #[]).run world)
 let mut matchCount := 0
 for row in oracle.queries.functionFacts.pointerAbis do
   let expected ← must (CallResolution.functionAbiId oracleRuntime row.abiId)
   unless actual.args.size == expected.args.size && actual.conv == expected.conv && actual.cVariadic == expected.cVariadic &&
     actual.fixedCount == expected.fixedCount && actual.canUnwind == expected.canUnwind do continue
   unless ← must (sameArgument after.arena oracleWorld.arena actual.ret expected.ret) do continue
   let mut same := true
   for (a,b) in actual.args.zip expected.args do
     unless ← must (sameArgument after.arena oracleWorld.arena a b) do same := false
   if same then matchCount := matchCount+1
 unless matchCount > 0 do throw (IO.userError s!"novel FnPtr has {matchCount} complete rustc ABI matchCount")
 IO.println s!"PASS novel array/reference/FnPtr ABI outside independent source prefix and without result catalogs ({matchCount} matching erased/HRTB oracle signatures)"
