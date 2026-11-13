import Miri.Input.CompilerInstanceAbi
import Miri.Input.Decoder
import Miri.Input.WorldObjectCandidate
import Miri.Input.WorldInstanceAbi

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameArg (aWorld bWorld : TypeArena.World) (a b : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
    (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) && a.layout.layout == b.layout.layout && a.mode == b.mode)
private def sameAbi (aWorld bWorld : TypeArena.World) (a b : Miri.ABI.FnAbi TypeId) : Except String Bool := do
  unless a.args.size == b.args.size && a.conv == b.conv && a.cVariadic == b.cVariadic &&
      a.fixedCount == b.fixedCount && a.canUnwind == b.canUnwind &&
      (← sameArg aWorld bWorld a.ret b.ret) do return false
  for (x,y) in a.args.zip b.args do unless ← sameArg aWorld bWorld x y do return false
  pure true

def main (args : List String) : IO Unit := do
  let [candidatePath,oraclePath] := args | throw (IO.userError "expected source Virtual candidate and pinned actual ABI oracle")
  let decoded := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
  let document := {decoded with types := decoded.types.map (fun node =>
    {node with compilerFacts := node.compilerFacts.map (fun facts => {facts with booleanQueries := #[],projectionQueries := none})})}
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let reference ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let referenceWorld ← must ((RuntimeArrayTypes.create reference).mapError reprStr)
  let queries := {metadata.source.queries with instanceAbis := #[],functionFacts :=
    {metadata.source.queries.functionFacts with types := #[],pointerAbis := #[],helperSignatures := #[]}}
  let stripped := {metadata.source with functionAbis := #[],queries}
  let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
  let base := {initial with instances := empty,bodies := BodyArena.Store.ofSource #[],metadata := {metadata with source := stripped}}
  let mut checked := 0
  let mut residual := 0
  for row in oracle.queries.instanceAbis do
    let some node := oracle.instances[row.instanceId]? | throw (IO.userError "oracle node missing")
    let .Virtual definition slot := node.instanceKind | continue
    let some declaration := oracle.definitions[definition]? | throw (IO.userError "oracle method missing")
    unless declaration.crateIndex == 0 do continue
    let terms ← must (GenericInstantiationWorld.ofArguments referenceWorld.arena 16384 node.genericArgs)
    let (actualArguments,world) ← must ((RuntimeArrayTypes.liftType
      (GenericInstantiationWorld.resolveArguments 16384 terms)).run base)
    let method ← must (world.arena.definitionRef ⟨declaration.crateIndex,declaration.index⟩)
    let (callee,selected) ← must ((WorldObjectCandidate.resolveOrdinary 100000 16384 method actualArguments).run world)
    let key ← must do
      match ← selected.instances.lookup callee with | .material key | .constructed key => pure key
    unless key.kind == .Virtual method slot && key.arguments == actualArguments do
      throw (IO.userError "normal source resolver differs from complete rustc Virtual key")
    let expected ← must (CallResolution.functionAbiId reference row.abiId)
    match (WorldVirtualAbi.construct callee #[]).run selected with
    | .ok _ => throw (IO.userError "tracked source ABI accepted missing-location-lang-item")
    | .error error => unless error.contains "caller-location raw lang-item identity mismatch" do
        throw (IO.userError s!"forged source recipe rejected at unrelated boundary: {error}")
    checked := checked + 1
  unless checked == 1 do throw (IO.userError "forged source recipe control coverage differs")
  IO.println "PASS missing-location-lang-item rejected at exact raw-source prerequisite"
