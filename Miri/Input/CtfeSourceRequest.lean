import Miri.Input.CtfeMirSource
import Miri.Input.CtfeQueryBridge
import Miri.Input.SourceEnvironment
import Miri.Input.GenericInstantiationWorld

/-! Source-only CTFE frame demand in one compiler universe. Query-root identity
and called-frame identity remain distinct. Preparing a frame grants no compiler
allocation, root-query result, validation or interning capability. -/
namespace Miri.Input.CtfeSourceRequest
open GenericSubstitution
structure Prepared where
  query : CtfeQueryBridge.QueryKey
  frame : InstanceArena.Key
  source : CtfeMirSource.Source
  /-- Instantiated source-explicit clauses, never a normalized ParamEnv. -/
  declarationClauses : Array TraitSelection.Clause
  constantArguments : Array Interpreter.CompileTime.CallFrame.ConstantArgument := #[]

private def verifyInstance (world : TypeArena.World) (key : InstanceArena.Key) : Except String Unit := do
  let verified ← InstanceArena.Key.ofSource world key.kind key.arguments
  unless verified == key do throw "CTFE instance key contradicts its current compiler universe"

/-- Initially only empty Codegen and its exact PostAnalysis retry environment
are connected. General source recipes must be derived in the current World. -/
def prepare (world : TypeArena.World) (environments : SourceEnvironment.Lookup)
    (sources : Array CtfeMirSource.Source) (origin : CompilerTypingEnv.Recipe)
    (query : CtfeQueryBridge.QueryKey) (frame : InstanceArena.Key) (promoted : Option Nat) :
    Except String Prepared := do
  let environment ← CompilerTypingEnv.deriveEmpty origin
  let retry ← CompilerTypingEnv.postAnalysisRetry environment
  unless query.environment == environment || retry == some query.environment do
    throw "CTFE query environment is outside the derived empty-Codegen/retry domain"
  verifyInstance world query.global.callee
  verifyInstance world frame
  let .Item _ := frame.kind | throw "scalar CTFE source policy requires an Item frame"
  let source ← CtfeMirSource.lookup sources frame.definition promoted
  if let .calls calls := source.program then
    let known (index : Nat) : Except String Unit := do
      let _ ← world.definitionRef ⟨0,index⟩
      pure ()
    let reference (value : Miri.Interpreter.CompileTime.CallFrame.Reference) : Except String Unit :=
      match value with
      | .parameterConstant .. => pure ()
      | .direct definition _ _ _ | .associated definition _ _ _ _ => known definition
    let operand (value : Miri.Interpreter.CompileTime.CallFrame.Operand) : Except String Unit :=
      match value with | .constant value => reference value | _ => pure ()
    for value in calls.required do reference value
    for block in calls.program.blocks do
      for statement in block.statements do
        match statement with
        | .assign _ (.use value _) => operand value
        | .assign _ (.binary _ left right) => operand left *> operand right
        | _ => pure ()
      match block.terminator with
      | .call call =>
        known call.callee
        for value in call.typeArguments do known value
        for value in call.arguments do operand value
      | .switch value _ _ => operand value
      | .assert value _ message _ =>
        operand value
        match message with
        | .overflow _ left right => operand left *> operand right
        | .divisionByZero value => operand value
      | _ => pure ()
  let material ← environments frame.definition
  unless material.parameters == source.parameters do throw "CTFE source generic scope contradicts canonical declaration material"
  let arguments ← GenericInstantiationWorld.ofArguments world 16384 frame.arguments
  let declarationClauses ← SourceEnvironment.instantiate environments 16384 frame.definition arguments
  let mut constantArguments := #[]
  if source.policy == .scalarU32ConstArgsV1 then
    let .calls calls := source.program | throw "const-args source payload absent"
    for parameter in calls.constantParameters do
      let some (.Const id) := frame.arguments[parameter.index]? | throw "constant parameter has no current-World const argument"
      let .Value ty tree ← world.lookupConstant id | throw "current-World const argument is not a source Value"
      let shape ← match ← world.lookupType ty with
        | .constructed constructor => pure (some constructor)
        | .material node => world.materialKey node
      unless shape == some (.integer false .u32) && parameter.ty == .uint 32 do
        throw "current-World constant argument type contradicts source u32 parameter"
      unless tree.root == 0 && tree.nodes.size == 1 do throw "current-World constant argument is not a scalar ValTree"
      let some (.Leaf bits bytes) := tree.nodes[tree.root]? | throw "current-World constant argument is not a scalar leaf"
      unless bytes == 4 && bits < 2^32 do throw "current-World constant argument width/range mismatch"
      constantArguments := constantArguments.push ⟨parameter.index,.uint 32,.uint 32 bits⟩
  pure ⟨query,frame,source,declarationClauses,constantArguments⟩
/-- Execute an explicitly prepared source frame, returning only a source candidate.
No compiler allocation, interning or query-success result is constructed here. -/
def enterSource (prepared : Prepared) (sources : Array CtfeMirSource.Source)
    (resolve : Array Nat → Interpreter.CompileTime.CallFrame.Reference → Except String Interpreter.CompileTime.CallFrame.Value)
    (arguments : Array Interpreter.CompileTime.CallFrame.Value) :
    Except String Unit × Interpreter.CompileTime.SourceStack.Machine := Id.run do
  let .ok programs := sources.mapM CtfeMirSource.stackSource
    | return (.error "source stack contains unsupported physical source identity",{})
  unless prepared.frame.arguments.isEmpty || prepared.source.policy == .scalarU32ConstArgsV1 do
    return (.error "source entry requires a separate physical type-argument adapter",{})
  return Interpreter.CompileTime.SourceStack.push programs resolve prepared.source.definition.index
    arguments #[] none {} prepared.constantArguments
end Miri.Input.CtfeSourceRequest
