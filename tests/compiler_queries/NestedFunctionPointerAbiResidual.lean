import Miri.Input.Decoder
import Miri.Input.CompilerFunctionFacts
open Miri.Input
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected nested unsupported FnPtr residual fixture")
 let source := (← must (decodeJson (← IO.FS.readFile path))).document
 let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
 let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let prepared ← must (CompilerFunctionFacts.prepare runtime (← must (lowerProgram source)))
 let mut checked := 0
 for row in source.queries.functionFacts.pointerAbis do
  let some node := source.types[row.typeId]? | throw (IO.userError "residual FnPtr type absent")
  let .functionPointer signature _ := node.shape | continue
  let #[child] := signature.inputs | continue
  unless (source.types[child]?).any (·.shapeKind == .functionPointer) do continue
  if ((WorldFunctionPointerAbi.construct row.typeId #[]).run world).isOk then
   throw (IO.userError "nested unsupported constructor escaped source reification boundary")
  let expected ← must (CallResolution.functionAbiId runtime row.abiId)
  let (actual,_) ← must ((CompilerFunctionFacts.pointerAbiInWorld prepared row.typeId #[]).run world)
  unless actual == expected do throw (IO.userError "nested FnPtr exact material residual differs from complete rustc ABI")
  let (novel,extended) ← must ((RuntimeArrayTypes.liftType (TypeArena.World.internType (.functionPointer {
   abiPacked := Miri.ABI.ExternAbi.asPacked .Rust,safe := true,cVariadic := false,splatted := none,
   inputs := #[child],output := source.queries.primitives.u16 }))).run world)
  unless novel >= world.arena.typeCount do throw (IO.userError "negative nested FnPtr key was not constructed")
  let forged := {prepared with pointerAbis := prepared.pointerAbis.push ⟨novel,#[],.ok row.abiId⟩}
  if ((CompilerFunctionFacts.pointerAbiInWorld forged novel #[]).run extended).isOk then
   throw (IO.userError "constructed unsupported nested FnPtr borrowed injected numeric material row")
  checked := checked+1
 unless checked > 0 do throw (IO.userError "unsupported nested FnPtr lost exact material ABI residuals")
 IO.println s!"PASS {checked} complete nested FnPtr rustc material residuals; constructed unsupported/injected numeric keys rejected"
