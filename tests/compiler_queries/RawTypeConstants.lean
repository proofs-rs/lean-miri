import Miri.Input.Decoder
import Miri.Input.WorldMirConstant
import Miri.Input.RuntimeArrayTypes
import Miri.Input.GenericInstantiationWorld

open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def assignedConstant (statement : Miri.MIR.Statement) : Option Miri.MIR.ConstOperand :=
  match statement.kind with
  | .Assign _ (.Use (.Constant constant) _) => some constant
  | _ => none

def main (args : List String) : IO Unit := do
  let [candidatePath,oraclePath] := args | throw (IO.userError "expected raw source and actual rustc oracle")
  let candidate := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let initial ← must (TypeArena.World.ofDocument candidate)
  let oracleWorld ← must (TypeArena.World.ofDocument oracle)
  let mut checked := 0
  for seed in candidate.bodies do
    let .material body := seed | continue
    let some instanceNode := candidate.instances[body.instanceId]?
      | throw (IO.userError "raw constant body instance is absent")
    let name := instanceNode.defPath.getD ""
    unless ["const_usize","const_signed","const_wide","const_bool","const_char"].any
        (· == name) do continue
    let matching := oracle.instances.filter (·.defPath == some name)
    let #[oracleInstance] := matching | throw (IO.userError "raw helper has no unique oracle instance")
    let key ← must (InstanceArena.Key.ofSource initial instanceNode.instanceKind instanceNode.genericArgs)
    let referenceKey ← must (InstanceArena.Key.ofSource oracleWorld oracleInstance.instanceKind oracleInstance.genericArgs)
    check (key.definition == referenceKey.definition &&
      (← must (GenericInstantiationWorld.ofArguments initial 16384 key.arguments)) ==
      (← must (GenericInstantiationWorld.ofArguments oracleWorld 16384 referenceKey.arguments)))
      "raw helper full instance identity differs from oracle"
    let some referenceIndex := oracleInstance.bodyId | throw (IO.userError "oracle helper has no body")
    let some (.material reference) := oracle.bodies[referenceIndex]?
      | throw (IO.userError "oracle helper body is not material")
    for (block,blockIndex) in body.mir.basicBlocks.zipIdx do
      for (statement,statementIndex) in block.statements.zipIdx do
        let some source := assignedConstant statement | continue
        let .Ty declared constantId := source.value | continue
        let some oracleStatement := (reference.mir.basicBlocks[blockIndex]?).bind
            (fun block => block.statements[statementIndex]?)
          | throw (IO.userError "raw constant source location has no oracle statement")
        let some expected := assignedConstant oracleStatement
          | throw (IO.userError "raw constant oracle is not a constant assignment")
        let .Val value expectedType := expected.value
          | throw (IO.userError "shadow did not retain actual rustc constant evaluation")
        let (ty,actual) ← must ((WorldMirConstant.evaluate initial source.span source.value).mapError reprStr)
        check (actual == value) "raw ValTree conversion differs from actual rustc Const::eval"
        check ((← must (GenericInstantiationWorld.ofType initial 16384 ty)) ==
          (← must (GenericInstantiationWorld.ofType oracleWorld 16384 expectedType)))
          "raw MIR constant lost its exact type"
        let _ ← must (initial.lookupConstant constantId)
        let wrongDeclared := if declared == candidate.queries.primitives.bool then
          candidate.queries.primitives.u8 else candidate.queries.primitives.bool
        let (sameType,sameValue) ← must ((WorldMirConstant.evaluate initial source.span
          (.Ty wrongDeclared constantId)).mapError reprStr)
        check (sameType == ty && sameValue == actual) "Const::ty did not prefer the Value's type"
        check (!(WorldMirConstant.evaluate initial source.span (.Ty declared initial.constantCount)).isOk)
          "missing raw type constant accepted"
        checked := checked + 1
  check (checked == 5) s!"expected five genuine Const::Ty assignments, found {checked}"
  let mut plainFunctions := 0
  let mut genericFunctions := 0
  for node in candidate.types do
    let .functionDefinition .. := node.shape | continue
    let some constructor ← must (initial.materialKey node)
      | throw (IO.userError "FnDef source identity is unavailable")
    let .functionDefinition _ arguments variables := constructor
      | throw (IO.userError "FnDef source acquired a different constructor")
    let value := WorldMirConstant.fromValue initial node.id ⟨#[.Branch #[]],0⟩
    if arguments.isEmpty && variables.isEmpty then
      match value with
      | .ok .ZeroSized => plainFunctions := plainFunctions + 1
      | _ => throw (IO.userError "closed FnDef ValTree did not produce exactly ZeroSized")
    else
      check (!value.isOk) "generic/bound FnDef bypassed the raw type-flag admission boundary"
      genericFunctions := genericFunctions + 1
  check (plainFunctions > 0 && genericFunctions > 0)
    "FnDef guard fixture lacks positive or unsupported-domain controls"
  let ty := candidate.queries.primitives.u8
  let badWidth : Miri.MIR.ValTree := ⟨#[.Leaf 7 2],0⟩
  check (!(WorldMirConstant.fromValue initial ty badWidth).isOk) "wrong primitive ValTree width accepted"
  let badTree : Miri.MIR.ValTree := ⟨#[.Leaf 7 1,.Leaf 9 1],0⟩
  check (!(WorldMirConstant.fromValue initial ty badTree).isOk) "unreachable ValTree nodes accepted"
  let unresolved : Miri.MIR.UnevaluatedConst := ⟨0,#[],none⟩
  check (!(WorldMirConstant.evaluate initial ⟨0⟩ (.Unevaluated unresolved ty)).isOk)
    "Unevaluated CTFE was replaced by a successful no-op"
  IO.println s!"PASS {checked} genuine raw Ty constants vs actual rustc evaluation; malformed and residual controls reject"
