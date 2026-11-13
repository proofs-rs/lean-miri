import Miri.Input.Decoder
import Miri.Input.CompilerFunctionFacts

open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path,typeText,countText,abiText] := args
    | throw (IO.userError "expected source, original FnDef type, argument count and ABI")
  let some ty := typeText.toNat? | throw (IO.userError "invalid original type")
  let some count := countText.toNat? | throw (IO.userError "invalid argument count")
  let expectedAbi ← match abiText with
    | "Rust" => pure Miri.ABI.ExternAbi.Rust
    | "RustCall" => pure Miri.ABI.ExternAbi.RustCall
    | _ => throw (IO.userError "unknown expected ABI")
  let decoded := (← must (decodeJson (← IO.FS.readFile path))).document
  let original ← must ((RuntimeMetadata.ofDocument decoded).mapError toString)
  let source := {decoded with functionAbis := #[],queries := {decoded.queries with
    instanceAbis := #[],functionFacts := {decoded.queries.functionFacts with
      types := #[],pointerAbis := #[],helperSignatures := #[]}}}
  let runtime := {original with source,checkedMaterial := none,denseTypes := none}
  let initial ← must ((RuntimeArrayTypes.create original).mapError reprStr)
  let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
  let world := {initial with instances := empty,bodies := BodyArena.Store.ofSource #[],metadata := runtime}
  let prepared ← must (CompilerFunctionFacts.prepare runtime (← must (lowerProgram source)))
  let (kind,_) ← must ((CompilerFunctionFacts.kindInWorld prepared ty).run world.arena)
  let .FnDef definition arguments := kind | throw (IO.userError "expected actual original FnDef")
  let (signature,_) ← must ((CompilerFunctionFacts.signatureInWorld prepared ty).run world)
  unless signature == (count,expectedAbi) do throw (IO.userError "original FnDef signature differs")
  if (CompilerFunctionFacts.signature prepared ty).isOk then
    throw (IO.userError "missing-table control retained a signature answer")
  let reject (probe : RuntimeArrayTypes.CompilerM GenericSubstitution.Term) := do
    if (probe.run world).isOk then throw (IO.userError "invalid raw signature request accepted")
  reject (InstanceSignature.instantiateDefinition 16384 source.definitions.size arguments)
  reject (InstanceSignature.instantiateDefinition 16384 definition (arguments.push (.Type ty)))
  let some declaration := source.definitions[definition]? | throw (IO.userError "definition absent")
  let missingDefinitions := source.definitions.set! definition {declaration with callableSource := none}
  let missingSource := {source with definitions := missingDefinitions}
  let missingRuntime := {runtime with source := missingSource, checkedMaterial := none, denseTypes := none}
  let noHeader := {world with metadata := missingRuntime}
  if ((InstanceSignature.instantiateDefinition 16384 definition arguments).run noHeader).isOk then
    throw (IO.userError "missing callable header accepted")
  let some node := source.types[ty]? | throw (IO.userError "original material FnDef absent")
  let .functionDefinition physical args signature bound _ := node.shape
    | throw (IO.userError "original type is not material FnDef")
  let malformed := {node with shape := .functionDefinition physical args signature bound #[.Region .Anon]}
  let badArena ← must (TypeArena.World.ofDocument {source with types := source.types.set! ty malformed})
  let badWorld := {world with arena := badArena}
  let tempting := {prepared with functions := #[⟨ty,none,.ok (count,expectedAbi)⟩]}
  match (CompilerFunctionFacts.signatureInWorld tempting ty).run badWorld with
  | .ok _ => throw (IO.userError "invalid FnDef argument binder escaped through legacy signature answer")
  | .error error => unless error.contains "FnDef call arguments retain a nonempty binder" do
      throw (IO.userError s!"invalid binder rejected at unrelated boundary: {error}")
  IO.println s!"PASS original FnDef type{ty} signature {count}/{abiText};empty instance/body/ABI/signature catalogs;physical definition,full arguments and callable header controls"
