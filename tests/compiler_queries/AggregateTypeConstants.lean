import Miri.Input.Decoder
import Miri.Input.WorldValTree
import Miri.Input.GenericInstantiationWorld

open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def assigned (statement : Miri.MIR.Statement) : Option Miri.MIR.ConstOperand :=
  match statement.kind with | .Assign _ (.Use (.Constant value) _) => some value | _ => none

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source aggregate constants and actual rustc oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let initial ← must (TypeArena.World.ofDocument source)
  let referenceWorld ← must (TypeArena.World.ofDocument oracle)
  let names := ["unit","empty_array","unit_array","empty_struct","aligned_struct",
    "scalar_tuple","scalar_wrapper","scalar_nested","scalar_tuple_nested","zero_nested"]
  let mut matched := #[]
  let mut scalar := 0
  let mut zeroCount := 0
  for seed in source.bodies do
    let .material body := seed | continue
    let some instanceNode := source.instances[body.instanceId]? | throw (IO.userError "source body instance missing")
    let name := instanceNode.defPath.getD ""
    unless names.contains name do continue
    let key ← must (InstanceArena.Key.ofSource initial instanceNode.instanceKind instanceNode.genericArgs)
    let references := oracle.instances.filter (·.defPath == some name)
    let #[reference] := references | throw (IO.userError "oracle helper instance is absent or ambiguous")
    let referenceKey ← must (InstanceArena.Key.ofSource referenceWorld reference.instanceKind reference.genericArgs)
    check (key.definition == referenceKey.definition &&
      (← must (GenericInstantiationWorld.ofArguments initial 16384 key.arguments)) ==
      (← must (GenericInstantiationWorld.ofArguments referenceWorld 16384 referenceKey.arguments)))
      "aggregate helper complete physical instance differs from oracle"
    let some referenceIndex := reference.bodyId | throw (IO.userError "aggregate oracle body missing")
    let some (.material referenceBody) := oracle.bodies[referenceIndex]? | throw (IO.userError "aggregate oracle is not material MIR")
    let mut found := false
    for (block,blockIndex) in body.mir.basicBlocks.zipIdx do
      for (statement,statementIndex) in block.statements.zipIdx do
        let some constant := assigned statement | continue
        let .Ty _ _ := constant.value | continue
        let some referenceStatement := (referenceBody.mir.basicBlocks[blockIndex]?).bind
            (fun block => block.statements[statementIndex]?)
          | throw (IO.userError "aggregate oracle statement missing")
        let some expected := assigned referenceStatement | throw (IO.userError "oracle statement is not a constant")
        let .Val expectedValue expectedType := expected.value | throw (IO.userError "oracle did not evaluate the source constant")
        let ((ty,value),world) ← must ((WorldValTree.evaluate runtime constant.span constant.value).run initial)
        check (value == expectedValue) s!"aggregate source conversion differs from actual rustc: {name}"
        check ((← must (GenericInstantiationWorld.ofType world 16384 ty)) ==
          (← must (GenericInstantiationWorld.ofType referenceWorld 16384 expectedType)))
          "aggregate conversion changed its outer type"
        match value with
        | .ZeroSized => zeroCount := zeroCount + 1
        | .Scalar (.Int ..) => scalar := scalar + 1
        | _ => throw (IO.userError "allocation-free source branch returned an allocation")
        check (!((WorldValTree.fromValue runtime 0 ty ⟨#[.Branch #[]],0⟩).run world).isOk)
          "exhausted aggregate conversion accepted"
        check (!((WorldValTree.fromValue runtime 16384 ty ⟨#[.Branch #[]],1⟩).run world).isOk)
          "aggregate conversion accepted an absent ValTree root"
        check (!((WorldValTree.fromValue runtime 16384 ty ⟨#[],0⟩).run world).isOk)
          "aggregate conversion accepted an absent source node"
        if let .Scalar _ := value then
          check (!((WorldValTree.fromValue runtime 16384 ty ⟨#[.Branch #[]],0⟩).run world).isOk)
            "scalar aggregate conversion accepted missing source fields"
        found := true
    check found s!"genuine Const::Ty assignment was not consumed: {name}"
    matched := matched.push name
  check (matched.size == 10 && scalar == 4 && zeroCount == 6)
    s!"incomplete aggregate source domain: {matched.size}/{scalar}/{zeroCount}"
  for name in ["residual_pair","residual_c"] do
    let matching := source.instances.filter (·.defPath == some name)
    let #[instanceNode] := matching | throw (IO.userError "aggregate residual instance missing")
    let some index := instanceNode.bodyId | throw (IO.userError "aggregate residual body missing")
    let some (.material body) := source.bodies[index]? | throw (IO.userError "aggregate residual body is not material")
    let constants := body.mir.basicBlocks.flatMap fun block => block.statements.filterMap assigned
    check (constants.any fun constant => match constant.value with
      | .Val (.Indirect ..) _ => true | _ => false)
      s!"non-scalar aggregate lost explicit CTFE allocation residual: {name}"
  IO.println "PASS ten actual aggregate ValTree conversions (six ZST/four scalar), exact types/instances and allocation residuals"
