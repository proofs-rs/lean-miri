import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi
open Miri.Input
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected Box ABI boundary fixture")
 let source := (← must (decodeJson (← IO.FS.readFile path))).document
 let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
 let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let prepared ← must (CompilerInstanceAbi.prepare runtime (← must (lowerProgram source)))
 let rows := source.instances.filter fun node => match node.instanceKind with
   | .Item id => ((source.definitions[id]?).bind (·.rawPath)).any fun path =>
     (path.components.back?.bind (·.name)) == some "residual"
   | _ => false
 let #[node] := rows | throw (IO.userError "unsupported BoxSlice residual source absent")
 if ((WorldInstanceAbi.construct node.id #[]).run world).isOk then
   throw (IO.userError "BoxSlice escaped the thin scalar Box capability boundary")
 let rows := source.queries.instanceAbis.filter (fun row => row.instanceId == node.id && row.extraArgumentTypes.isEmpty)
 let #[row] := rows | throw (IO.userError "unsupported BoxSlice lost its exact material ABI")
 let expected ← must (CallResolution.functionAbiId runtime row.abiId)
 let (actual,_) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared node.id #[]).run world)
 unless actual == expected do throw (IO.userError "BoxSlice residual differs from complete compiler ABI")
 let empty ← must (InstanceArena.Store.ofSource world.arena #[])
 let key ← must (InstanceArena.Key.ofSource world.arena node.instanceKind node.genericArgs)
 let (callee,instances) ← must (empty.intern world.arena key)
 unless callee == 0 do throw (IO.userError "constructed unsupported Box key not densely interned")
 if ((CompilerInstanceAbi.abiOfInstanceInWorld prepared callee #[]).run {world with instances}).isOk then
   throw (IO.userError "constructed unsupported Box borrowed unrelated material-prefix numeric ABI")
 let ordinary := source.instances.filter fun node => match node.instanceKind with
   | .Item id => ((source.definitions[id]?).bind (·.rawPath)).any fun path =>
     (path.components.back?.bind (·.name)) == some "identity"
   | _ => false
 let some ordinary := ordinary[0]? | throw (IO.userError "thin Box source key absent")
 let wrongWidth := {world with metadata := {world.metadata with
   target := {world.metadata.target with defaultAddressSpacePointerSpec :=
     {world.metadata.target.defaultAddressSpacePointerSpec with pointerSize := Miri.ABI.Size.ofBytes 4}},checkedMaterial := none}}
 if ((WorldInstanceAbi.construct ordinary.id #[]).run wrongWidth).isOk then
   throw (IO.userError "thin Box ABI accepted a non-64-bit target")
 let wrongArch := {world with metadata := {world.metadata with source :=
   {world.metadata.source with producer := {world.metadata.source.producer with targetTriple := "aarch64-unknown-linux-gnu"}}}}
 if ((WorldInstanceAbi.construct ordinary.id #[]).run wrongArch).isOk then
   throw (IO.userError "thin Box ABI accepted an unported architecture")
 IO.println "PASS unsupported BoxSlice exact residual; constructed/numeric collision, pointer width and architecture boundaries"
