import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi
open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameArgument (aWorld bWorld : TypeArena.World)
    (a b : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
    (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) &&
    a.layout.layout == b.layout.layout && a.mode == b.mode)
private def sameAbi (aWorld bWorld : TypeArena.World)
    (a b : Miri.ABI.FnAbi TypeId) : Except String Bool := do
  unless a.args.size == b.args.size && a.conv == b.conv && a.cVariadic == b.cVariadic &&
      a.fixedCount == b.fixedCount && a.canUnwind == b.canUnwind &&
      (← sameArgument aWorld bWorld a.ret b.ret) do return false
  for (x,y) in a.args.zip b.args do
    unless ← sameArgument aWorld bWorld x y do return false
  pure true

def main (args : List String) : IO Unit := do
  let [path,oraclePath] := args | throw (IO.userError "expected external ABI candidate/oracle")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let reference ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let oracleWorld ← must ((RuntimeArrayTypes.create reference).mapError reprStr)
  let prepared ← must (CompilerInstanceAbi.prepare runtime (← must (lowerProgram document)))
  let mut indirect := 0
  let mut direct := 0
  for row in oracle.queries.instanceAbis do
    let some node := oracle.instances[row.instanceId]? | throw (IO.userError "missing oracle instance")
    let .Item definition := node.instanceKind | continue
    let some decl := oracle.definitions[definition]? | continue
    unless decl.crateIndex != 0 && ["identity","accept_pair"].any
        (fun name => (decl.rawPath.bind fun path => path.components.back?.bind (·.name)) == some name) do continue
    let arguments ← must (GenericInstantiationWorld.ofArguments oracleWorld.arena 16384 node.genericArgs)
    let sources ← must (document.instances.filterM fun source => do
      let key ← InstanceArena.Key.ofSource initial.arena source.instanceKind source.genericArgs
      pure (key.definition == ⟨decl.crateIndex,decl.index⟩ &&
        (← GenericInstantiationWorld.ofArguments initial.arena 16384 key.arguments) == arguments))
    let #[source] := sources | throw (IO.userError "external source key is not unique")
    let expected ← must (CallResolution.functionAbiId reference row.abiId)
    let needsIndirect := (expected.args.push expected.ret).any fun arg =>
      match arg.mode with | .Indirect .. => true | _ => false
    let rows := document.queries.instanceAbis.filter (·.instanceId == source.id)
    let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
    let key ← must (InstanceArena.Key.ofSource initial.arena source.instanceKind source.genericArgs)
    let (callee,instances) ← must (empty.intern initial.arena key)
    let stripped := {runtime.source with functionAbis := #[],queries := {runtime.source.queries with instanceAbis := #[]}}
    let world := {initial with
      instances
      bodies := BodyArena.Store.ofSource #[]
      metadata := {runtime with source := stripped}}
    if needsIndirect then
      unless rows.size == 1 do throw (IO.userError "external indirect ABI lost exact material row")
      match (WorldInstanceAbi.construct callee #[]).run world with
      | .error error => do
        unless error.contains "original-crate deduction policy" do
          throw (IO.userError s!"external indirect rejected for wrong reason: {error}")
      | .ok _ => throw (IO.userError "external indirect used current-session deduction policy")
      indirect := indirect + 1
    else
      unless rows.isEmpty do throw (IO.userError "prior external direct domain retained an eager ABI")
      let (actual,after) ← must ((WorldInstanceAbi.construct callee #[]).run world)
      unless ← must (sameAbi after.arena oracleWorld.arena actual expected) do
        throw (IO.userError "external direct ABI differs from rustc")
      direct := direct + 1
    let (actual,after) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared source.id #[]).run initial)
    unless ← must (sameAbi after.arena oracleWorld.arena actual expected) do
      throw (IO.userError "external source/direct or exact indirect residual differs from rustc")
  unless indirect == 3 && direct == 3 do throw (IO.userError s!"wrong external coverage {indirect}/{direct}")
  IO.println "PASS3constructed external indirect policy rejections before session guards,3preserved external direct domains,6complete ABI matches"
