import Miri.Input.Decoder
import Miri.Input.CtfeSourceRequest
open Lean Miri.Input Miri.Interpreter.CompileTime
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path,input,tiny,deny] := args | throw (IO.userError "source input tiny deny")
  let some input := input.toNat? | throw (IO.userError "source input")
  let json ← must (Json.parse (← IO.FS.readFile path))
  let (sources,definitions,world) ← if (json.getObjVal? "ctfe_scalar_sources").isOk then do
    let decoded ← must (decodeJson json.compress)
    let document := decoded.document
    let world ← must (TypeArena.World.ofDocument document)
    pure (document.ctfeScalarSources,document.definitions,world)
  else do
    let raw ← must (json.getObjValAs? (Array Json) "sources")
    let sources ← must (raw.mapM CtfeMirSourceCodec.read)
    let definitions := sources.map fun source => ({
      crateIndex := source.definition.crateIndex,index := source.definition.index
      sourceEnvironment := some {parameters := source.parameters,parent := none,genericParent := none,isTrait := false,ownPredicates := #[]}} : DefinitionId)
    let world ← must (TypeArena.World.ofMaterial #[] #[] definitions #[] 8)
    pure (sources,definitions,world)
  unless sources.any (·.policy == .scalarU32ConstArgsV1) do
    throw (IO.userError "constargs catalogue absent")
  let (ty,world) ← must ((TypeArena.World.internType (.integer false .u32)).run world)
  let (constant,world) ← must ((TypeArena.World.internConstant (.Value ty ⟨#[.Leaf input 4],0⟩)).run world)
  unless constant ≥ world.materialConstants.size do throw (IO.userError "constant unexpectedly material")
  let environments : SourceEnvironment.Lookup := fun definition => do
    let index ← world.definitionRef definition
    let some node := definitions[index]? | throw "definition absent"
    let some header := node.sourceEnvironment | throw "header absent"
    pure header
  let programs ← must (sources.mapM CtfeMirSource.stackSource)
  let config : Counter.Config := ⟨64,tiny == "1",deny == "1"⟩
  let resolve := SourceStack.sourceConstant programs #[] config 100
  for source in sources do
    if source.policy != .scalarU32ConstArgsV1 then continue
    let frame ← must (InstanceArena.Key.item world source.definition #[.Const constant])
    let query : CtfeQueryBridge.QueryKey := ⟨.allocation,CompilerTypingEnv.fullyMonomorphized,⟨frame,none⟩⟩
    let prepared ← must (CtfeSourceRequest.prepare world environments sources .fullyMonomorphized query frame none)
    unless prepared.constantArguments == #[⟨0,.uint 32,.uint 32 input⟩] do throw (IO.userError "World constant argument lost its typed namespace")
    let (entered,machine) := CtfeSourceRequest.enterSource prepared sources resolve #[]
    must entered
    unless machine.requiredRequests.size == 1 do throw (IO.userError "raw required Param occurrence omitted")
    match SourceStack.run programs config resolve 1000000 machine with
    | .returned (.uint 32 value) machine => IO.println s!"candidate\t{source.definition.index}\t{value}\t{machine.steps}\t{machine.counters}"
    | .failed error machine => IO.println s!"source-error\t{source.definition.index}\t{error}\t{machine.steps}\t{machine.counters}"
    | _ => throw (IO.userError "unexpected source frame result")
    -- These are source inputs in a constructed World, not allocation-query results.
    let (bad,worldBad) ← must ((TypeArena.World.internConstant (.Value ty ⟨#[.Leaf input 1],0⟩)).run world)
    let badFrame ← must (InstanceArena.Key.item worldBad source.definition #[.Const bad])
    unless !(CtfeSourceRequest.prepare worldBad environments sources .fullyMonomorphized query badFrame none).isOk do
      throw (IO.userError "wrong constant byte width accepted")
    let wrongFrame ← must (InstanceArena.Key.item world source.definition #[.Type ty])
    unless !(CtfeSourceRequest.prepare world environments sources .fullyMonomorphized query wrongFrame none).isOk do
      throw (IO.userError "type ID accepted in constant argument namespace")
    let .calls program := source.program | throw (IO.userError "payload absent")
    let missing := {program with constantParameters := #[]}
    unless !(SourceStack.validateSource missing).isOk do throw (IO.userError "missing Param declaration accepted")
    let hole := {program with constantParameters := #[⟨1,.uint 32⟩]}
    unless !(SourceStack.validateSource hole).isOk do throw (IO.userError "physical generic index hole accepted")
