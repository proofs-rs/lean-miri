import Miri.Input.Decoder
import Miri.Input.CompilerWorldFacts
open Miri.Input
private def must (value : Except String α) : IO α :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected actual Box type metadata")
 let document := (← must (decodeJson (← IO.FS.readFile path))).document
 let original ← must ((RuntimeMetadata.ofDocument document).mapError toString)
 let types := original.source.types.map fun node => {node with compilerFacts := node.compilerFacts.map fun facts =>
   {facts with booleanQueries := #[]}}
 let runtime ← must ((RuntimeMetadata.ofDocument {original.source with types}).mapError toString)
 let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
 let context : CompilerFacts.Context := ⟨runtime,← must (lowerProgram runtime.source),none⟩
 let mut globalCases := 0
 let mut customCases := 0
 for node in document.types do
  let .adt data := node.shape | continue
  unless ((document.definitions[data.definition]?).bind (·.adtDeclaration)).any
    (·.langItem == some "owned_box") do continue
  let some expected := node.compilerFacts.bind fun facts =>
    (facts.booleanQueries.find? (·.1 == "is_global_box")).map (·.2)
    | throw (IO.userError "actual rustc Box allocator-identity control missing")
  let (actual,_) ← must ((CompilerFacts.booleanInWorld context node.id "is_global_box").run world.arena)
  unless actual == expected do throw (IO.userError s!"raw allocator lang-item identity differs from actual rustc for Box {node.id}")
  if expected then globalCases := globalCases+1 else customCases := customCases+1
 unless globalCases > 0 && customCases > 0 do throw (IO.userError "Box oracle lacks global/custom same-name allocator controls")
 IO.println s!"PASS Box global allocator raw identity matches {globalCases} global/{customCases} custom actual controls with all boolean answers removed"
