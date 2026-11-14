import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi
open Miri.Input
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected Box allocator boundary source")
 let source := (← must (decodeJson (← IO.FS.readFile path))).document
 let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
 let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let prepared ← must (CompilerInstanceAbi.prepare runtime (← must (lowerProgram source)))
 for name in ["residual_aligned","residual_payload"] do
  let nodes := source.instances.filter fun node => match node.instanceKind with
   | .Item id => ((source.definitions[id]?).bind (·.rawPath)).any fun path => (path.components.back?.bind (·.name)) == some name
   | _ => false
  let #[node] := nodes | throw (IO.userError s!"missing allocator boundary {name}")
  let rows := source.queries.instanceAbis.filter fun row => row.instanceId == node.id && row.extraArgumentTypes.isEmpty
  let #[row] := rows | throw (IO.userError s!"unadmitted allocator {name} lost exact ABI residual")
  let expected ← must (CallResolution.functionAbiId runtime row.abiId)
  let (actual,_) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared node.id #[]).run world)
  unless actual == expected do throw (IO.userError s!"allocator {name} complete compiler ABI differs")
 IO.println "PASS non-ZST and over-aligned allocator Box signatures preserve exact complete material ABI residuals"
