import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def equalArgument (leftWorld rightWorld : TypeArena.World)
    (left right : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  let a ← GenericInstantiationWorld.ofType leftWorld 16384 left.layout.ty
  let b ← GenericInstantiationWorld.ofType rightWorld 16384 right.layout.ty
  pure (a == b && left.layout.layout == right.layout.layout && left.mode == right.mode)

def main (args : List String) : IO Unit := do
  let [basePath,oraclePath] := args | throw (IO.userError "expected independent base and reference oracle exports")
  let base := (← must (decodeJson (← IO.FS.readFile basePath))).document
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument base).mapError toString)
  let oracleMetadata ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let oracleWorld ← must ((RuntimeArrayTypes.create oracleMetadata).mapError reprStr)
  let definitions := base.definitions.zipIdx.filter fun (source,_) =>
    (source.rawPath.bind fun path => path.components.back?.bind (·.name)) == some "identity"
  let #[(definition,definitionId)] := definitions | throw (IO.userError "base identity declaration is not unique")
  let identity : GenericSubstitution.DefinitionIdentity := ⟨definition.crateIndex,definition.index⟩
  let referenceRows := oracle.queries.instanceAbis.filter fun row =>
    match oracle.instances[row.instanceId]? with
    | some source => match source.instanceKind with
      | .Item id => (oracle.definitions[id]?).any fun source =>
          source.crateIndex == identity.crateIndex && source.index == identity.index
      | _ => false
    | none => false
  let #[row] := referenceRows | throw (IO.userError "reference oracle does not have one complete identity ABI")
  let (reference,constructed) ← must ((RuntimeArrayTypes.liftType do
    let length ← TypeArena.World.internConstant (.Value base.queries.primitives.usize
      ⟨#[.Leaf 13 initial.arena.pointerBytes],0⟩)
    let array ← TypeArena.World.internType (.array base.queries.primitives.u8 length)
    unless array >= initial.arena.typeCount do throw "array was already material in the independent base"
    let reference ← TypeArena.World.internType (.reference array .Mut .Erased)
    unless reference >= initial.arena.typeCount do throw "reference was already material in the independent base"
    pure reference).run initial)
  let empty ← must (InstanceArena.Store.ofSource constructed.arena #[])
  let key ← must (InstanceArena.Key.ofSource constructed.arena (.Item definitionId) #[.Type reference])
  let (callee,instances) ← must (empty.intern constructed.arena key)
  let source := {metadata.source with
    functionAbis := #[]
    queries := {metadata.source.queries with instanceAbis := #[]}}
  let world := {constructed with instances, metadata := {metadata with source}}
  let (actual,after) ← must ((WorldInstanceAbi.construct callee #[]).run world)
  let expected ← must (CallResolution.functionAbiId oracleMetadata row.abiId)
  unless actual.args.size == expected.args.size && actual.conv == expected.conv &&
      actual.cVariadic == expected.cVariadic && actual.fixedCount == expected.fixedCount &&
      actual.canUnwind == expected.canUnwind do throw (IO.userError "novel reference ABI interface differs from rustc")
  unless ← must (equalArgument after.arena oracleWorld.arena actual.ret expected.ret) do
    throw (IO.userError "novel reference return ABI differs from rustc")
  for (a,b) in actual.args.zip expected.args do
    unless ← must (equalArgument after.arena oracleWorld.arena a b) do
      throw (IO.userError "novel reference argument ABI differs from rustc")
  IO.println "PASS independent novel array/reference/instance IDs with no ABI result catalogs match complete rustc ABI"
