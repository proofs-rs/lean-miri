import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi
import Miri.Input.WorldSignatureAbi

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def equalArgument (leftWorld rightWorld : TypeArena.World)
    (left right : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  let a ← GenericInstantiationWorld.ofType leftWorld 16384 left.layout.ty
  let b ← GenericInstantiationWorld.ofType rightWorld 16384 right.layout.ty
  pure (a == b && left.layout.layout == right.layout.layout && left.mode == right.mode)

def main (args : List String) : IO Unit := do
  let [basePath,oraclePath] := args | throw (IO.userError "expected independent indirect array base/oracle")
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
  let #[row] := rows | throw (IO.userError "indirect array oracle lacks unique identity complete ABI")
  let (array,constructed) ← must ((RuntimeArrayTypes.liftType do
    let length ← TypeArena.World.internConstant (.Value base.queries.primitives.usize ⟨#[.Leaf 11 initial.arena.pointerBytes],0⟩)
    let array ← TypeArena.World.internType (.array base.queries.primitives.u8 length)
    unless array >= initial.arena.typeCount do throw "array was already material in independent base"
    pure array).run initial)
  let empty ← must (InstanceArena.Store.ofSource constructed.arena #[])
  let key ← must (InstanceArena.Key.ofSource constructed.arena (.Item definitionId) #[.Type array])
  let (callee,instances) ← must (empty.intern constructed.arena key)
  let facts := {metadata.source.queries.functionFacts with helperSignatures := #[],pointerAbis := #[],types := #[]}
  let queries := {metadata.source.queries with instanceAbis := #[],functionFacts := facts}
  let source := {metadata.source with functionAbis := #[],queries}
  let world := {constructed with
    instances
    bodies := BodyArena.Store.ofSource #[]
    metadata := {metadata with source}}
  let (actual,after) ← must ((WorldInstanceAbi.construct callee #[]).run world)
  let expected ← must (CallResolution.functionAbiId reference row.abiId)
  unless actual.args.size == expected.args.size && actual.conv == expected.conv && actual.cVariadic == expected.cVariadic &&
    actual.fixedCount == expected.fixedCount && actual.canUnwind == expected.canUnwind do throw (IO.userError "novel indirect array ABI interface differs")
  unless ← must (equalArgument after.arena oracleWorld.arena actual.ret expected.ret) do throw (IO.userError "novel indirect array return ABI differs from actual rustc")
  for (a,b) in actual.args.zip expected.args do
    unless ← must (equalArgument after.arena oracleWorld.arena a b) do throw (IO.userError "novel indirect array argument ABI differs from actual rustc")
  let wanted ← must (GenericInstantiationWorld.ofType constructed.arena 16384 array)
  let pointerRows ← must (oracle.queries.functionFacts.pointerAbis.filterM fun row => do
    let signature ← WorldFunctionPointerAbi.sourceSignature oracleWorld.arena row.typeId
    pure (signature.inputs == #[wanted] && signature.output == wanted))
  let #[pointerRow] := pointerRows | throw (IO.userError "novel indirect FnPtr oracle is not unique")
  let pointerExpected ← must (CallResolution.functionAbiId reference pointerRow.abiId)
  let (pointer,pointerWorld) ← must ((RuntimeArrayTypes.liftType do
    let pointer ← TypeArena.World.internType (.functionPointer {
      abiPacked := Miri.ABI.ExternAbi.asPacked .Rust, safe := true, cVariadic := false,
      splatted := none,inputs := #[array],output := array})
    unless pointer >= initial.arena.typeCount do throw "novel indirect FnPtr was material in base"
    pure pointer).run world)
  let (pointerActual,pointerAfter) ← must ((WorldFunctionPointerAbi.construct pointer #[]).run pointerWorld)
  let (helperActual,helperAfter) ← must ((WorldSignatureAbi.query
    ⟨#[array],array,.Rust,.Safe,false,false⟩).run pointerWorld)
  for (actual,retained) in #[(pointerActual,pointerAfter),(helperActual,helperAfter)] do
    unless actual.args.size == pointerExpected.args.size && actual.conv == pointerExpected.conv &&
        actual.cVariadic == pointerExpected.cVariadic && actual.fixedCount == pointerExpected.fixedCount &&
        actual.canUnwind == pointerExpected.canUnwind &&
        (← must (equalArgument retained.arena oracleWorld.arena actual.ret pointerExpected.ret)) do
      throw (IO.userError "novel indirect FnPtr/helper ABI interface or return differs")
    for (arg,referenceArg) in actual.args.zip pointerExpected.args do
      unless ← must (equalArgument retained.arena oracleWorld.arena arg referenceArg) do
        throw (IO.userError "novel indirect FnPtr/helper ABI argument differs")
  IO.println "PASS novel indirect array/Item/body/FnPtr/helper identities outside prefix with all ABI catalogs removed match complete rustc ABI"
