import Miri
open Lean Miri.Input Miri.ABI Miri.Interpreter
private def must [Repr ε] (value : Except ε α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError (reprStr error))
private def access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ world => world⟩
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current transparent1 candidate")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let some byte := document.types.find? (fun node =>
    node.shapeKind == .uint && node.shapeMetadata.unsignedKind == some (.known .u8))
    | throw (IO.userError "fixture lacks actual u8 poison identity")
  let document := {document with types := document.types.map fun node =>
    {node with compilerFacts := none,shape := match node.shape with
      | .adt data => .adt {data with variants := data.variants.map fun variant =>
          {variant with fields := variant.fields.map fun field => {field with name := "__poisoned",typeId := byte.id}}}
      | shape => shape}}
  let runtime ← must (RuntimeMetadata.ofDocument document)
  let original ← must (RuntimeArrayTypes.create runtime)
  let term ← must (GenericInstantiationWorld.ofType original.arena runtime.materialLayoutFuel 1)
  let empty ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] runtime.target.pointerSize.bytes.toNat)
  let instances ← must (InstanceArena.Store.ofSource empty #[])
  let constructed := {original with arena := empty,instances,bodies := BodyArena.Store.ofSource #[]}
  for initial in #[original,constructed] do
    let (owner,world) ← must (RuntimeArrayTypes.perform initial (GenericInstantiationWorld.resolveType runtime.materialLayoutFuel term))
    let (parent,world) ← must (RuntimeArrayTypes.perform world (RuntimeMetadata.layoutInWorld runtime owner))
    let query := CompilerNamedFields.fieldIndex access parent "0"
    match query world with
    | .error error _ => throw (IO.userError s!"actual named source field failed: {reprStr error}")
    | .ok index after =>
      check (index == 0) "raw source field name selected wrong logical index"
      check (after.arena.materialTypes.size == initial.arena.materialTypes.size) "query changed the material prefix"
      match CompilerNamedFields.fieldIndex access parent "absent" after with
      | .error (.invalidProgram _) _ => pure ()
      | _ => throw (IO.userError "required missing raw field did not fail")
  IO.println "NamedFields source callback material/constructed owner, exact name, raw cached names/types poisoned, and required absence failure PASS"
