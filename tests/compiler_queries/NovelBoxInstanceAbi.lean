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
  let [basePath,oraclePath,allocatorKind] := args | throw (IO.userError "expected independent Box base/oracle and global/custom")
  let base := (← must (decodeJson (← IO.FS.readFile basePath))).document
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument base).mapError toString)
  let reference ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let oracleWorld ← must ((RuntimeArrayTypes.create reference).mapError reprStr)
  let definitions := base.definitions.zipIdx.filter fun (source,_) => source.crateIndex == 0 &&
    (source.rawPath.bind fun path => path.components.back?.bind (·.name)) == some "identity"
  let #[(definition,definitionId)] := definitions | throw (IO.userError "base identity declaration is not unique")
  let identity : GenericSubstitution.DefinitionIdentity := ⟨definition.crateIndex,definition.index⟩
  let rows := oracle.queries.instanceAbis.filter fun row =>
    match oracle.instances[row.instanceId]? with
    | some source => match source.instanceKind with
      | .Item id => (oracle.definitions[id]?).any fun source => source.crateIndex == identity.crateIndex && source.index == identity.index
      | _ => false
    | none => false
  let #[row] := rows | throw (IO.userError "Box oracle lacks unique identity complete ABI")
  let mut chosen : Option AdtShape := none
  for node in base.types do
    let .adt data := node.shape | continue
    unless ((base.definitions[data.definition]?).bind (·.adtDeclaration)).any (·.langItem == some "owned_box") do continue
    let some (Miri.MIR.GenericArg.Type pointee) := data.args[0]? | continue
    unless (base.types[pointee]?).any (fun node => match node.shape with | .tuple fields => fields.isEmpty | _ => false) do continue
    let some (Miri.MIR.GenericArg.Type allocator) := data.args[1]? | continue
    let some allocator := base.types[allocator]? | continue
    let .adt allocator := allocator.shape | continue
    let global := ((base.definitions[allocator.definition]?).bind (·.adtDeclaration)).any (·.langItem == some "global_alloc_ty")
    unless global == (allocatorKind == "global") do continue
    if chosen.isSome then throw (IO.userError "duplicate base Box constructor for allocator class")
    chosen := some data
  let some data := chosen | throw (IO.userError "missing base Box<Unit,allocator> raw constructor")
  let (box,constructed) ← must ((RuntimeArrayTypes.liftType do
    let length ← TypeArena.World.internConstant (.Value base.queries.primitives.usize ⟨#[.Leaf 13 initial.arena.pointerBytes],0⟩)
    let array ← TypeArena.World.internType (.array base.queries.primitives.u8 length)
    unless array >= initial.arena.typeCount do throw "array was already present in independent Box base"
    let definition ← (← get).identity data.definition
    let arguments := data.args.mapIdx fun index argument => if index == 0 then Miri.MIR.GenericArg.Type array else argument
    let box ← TypeArena.World.internType (.adt definition arguments)
    unless box >= initial.arena.typeCount do throw "Box was already material in the independent base"
    pure box).run initial)
  let empty ← must (InstanceArena.Store.ofSource constructed.arena #[])
  let key ← must (InstanceArena.Key.ofSource constructed.arena (.Item definitionId) #[.Type box])
  let (callee,instances) ← must (empty.intern constructed.arena key)
  let source := {metadata.source with functionAbis := #[],queries := {metadata.source.queries with instanceAbis := #[]}}
  let world := {constructed with instances,metadata := {metadata with source}}
  let (actual,after) ← must ((WorldInstanceAbi.construct callee #[]).run world)
  let expected ← must (CallResolution.functionAbiId reference row.abiId)
  unless actual.args.size == expected.args.size && actual.conv == expected.conv && actual.cVariadic == expected.cVariadic &&
    actual.fixedCount == expected.fixedCount && actual.canUnwind == expected.canUnwind do throw (IO.userError "novel Box ABI interface differs")
  unless ← must (equalArgument after.arena oracleWorld.arena actual.ret expected.ret) do throw (IO.userError "novel Box return ABI differs from actual rustc")
  for (a,b) in actual.args.zip expected.args do
    unless ← must (equalArgument after.arena oracleWorld.arena a b) do throw (IO.userError "novel Box argument ABI differs from actual rustc")
  IO.println s!"PASS novel array/Box/{allocatorKind}-allocator/instance IDs outside prefix with no ABI catalogs match complete rustc ABI"
