import Lean.Util.Profile
import Miri.Input.CompilerInstance
import Miri.Input.NormalizationBody
import Miri.Interpreter.OperandPath
import Miri.Input.RuntimeMetadata
import Miri.Interpreter.Constant

/-! Checked reuse of real rustc normalization and Const::eval query results.
Sources: ty/instance.rs::try_instantiate_mir_and_normalize_erasing_regions;
mir/consts.rs::Const::eval; Miri operand.rs::eval_const_to_op. A query key
contains the complete instance, source body, MIR location and structural operand
path. A source span alone is never an identity. Missing or malformed compiler
metadata remains an error when requested. -/
namespace Miri.Input.CompilerConstantQueries
open Lean Miri.Interpreter

abbrev PathElement := OperandPathElement
structure Site where
  bodyIndex : Nat
  location : MIR.Location
  path : Array PathElement
  deriving Repr, DecidableEq
structure Evidence where
  site : Site
  query : CompilerConstantEvidence
  sourceOperand : MIR.ConstOperand
  normalizedOperand : MIR.ConstOperand
structure Prepared where
  program : LoweredProgram
  evidence : Array Evidence
  obligations : Array Obligation

private def sourceConstants (bodyIndex : Nat) (body : BodyCore) : Array (Site × ConstantFact) := Id.run do
  let mut found := #[]
  for (block, blockIndex) in body.nodeFacts.toList.zipIdx do
    for (node, statementIndex) in block.toList.zipIdx do
      for fact in node.constants do
        found := found.push (⟨bodyIndex, ⟨blockIndex,statementIndex⟩, fact.path⟩,fact)
  return found

private def normalizedOperand (body : BodyCore) (site : Site) : Except String ConstantFact := do
  let some block := body.nodeFacts[site.location.block]? | throw "normalized block is absent"
  let some node := block[site.location.statementIndex]? | throw "normalized instruction is absent"
  let some fact := node.constants.find? (·.path == site.path) | throw "normalized constant site is absent"
  pure fact

private def evidenceAt (_ctx : LowerContext) (tables : CompilerTables) (fnInstance : CallInstance)
    (site : Site) (original normalized : ConstantFact) : Except String (Evidence × CompilerTables) := do
  unless original.operand.span == normalized.operand.span do throw "normalization changed constant source span"
  pure (⟨site, ⟨fnInstance,original.operand.value,normalized.operand.value,normalized.operand.span,
    normalized.evaluated⟩, original.operand, normalized.operand⟩, tables)

private structure PrepareState where
  tables : CompilerTables
  evidence : Array Evidence
  obligations : Array Obligation

private def prepareBody (ctx : LowerContext)
    (program : LoweredProgram) (bodyIndex : Nat) (state : PrepareState) :
    Except String PrepareState := do
  let some body := program.bundle.bodies[bodyIndex]? | throw "body index missing"
  match body.input.constantQueryContext with
  | none =>
    let obligation : Obligation := ⟨s!"bodies[{bodyIndex}].constant_query_context",
      "compiler current-instance normalization query is missing"⟩
    pure { state with obligations := state.obligations.push obligation }
  | some queryContext => do
    let fnInstance := queryContext.instanceId
    unless fnInstance < ctx.instances.size do throw "constant query instance ID out of bounds"
    let tables := state.tables
    let normalizedBody ← NormalizationBody.resolve queryContext.normalizationBodyId program.input.bodies
    let mut tables := tables
    let mut evidence := state.evidence
    let mut obligations := state.obligations
    for (site,original) in sourceConstants bodyIndex body.input do
      let result := do
        let normalized ← normalizedOperand normalizedBody.toBodyCore site
        evidenceAt ctx tables fnInstance site original normalized
      match result with
      | .ok (entry,nextInterner) =>
        evidence := evidence.push entry
        tables := nextInterner
      | .error message =>
        obligations := obligations.push
          ⟨s!"bodies[{bodyIndex}].constant[{reprStr site.location},{reprStr site.path}]",message⟩
    pure ⟨tables,evidence,obligations⟩

private def prepareBodies (ctx : LowerContext) (program : LoweredProgram)
    (initial : PrepareState) : Except String PrepareState := do
  let mut state := initial
  for bodyIndex in program.executableBodyIds do
    state ← prepareBody ctx program bodyIndex state
  pure state

/-- Build only from explicit exporter compiler-query context. In particular,
monomorphic-looking syntax is never taken as evidence of normalization. -/
def prepareProfiled (profile : Lean.Options) (input : LoweredProgram) : Except String Prepared := do
  let program := profileit "preparation.constants.globals" profile fun _ =>
    CompilerGlobals.prepareProgram input
  let ctx := profileit "preparation.constants.context" profile fun _ =>
    LowerContext.ofDocument program.input
  let initial : PrepareState := ⟨program.compilerTables, #[], #[]⟩
  let state ← profileit "preparation.constants.bodies" profile fun _ =>
    prepareBodies ctx program initial
  let program := program.withCompilerTables state.tables
  pure ⟨program,state.evidence,state.obligations⟩

def prepare (input : LoweredProgram) : Except String Prepared := prepareProfiled {} input

/-- Bind the exact interpreter source site before evaluation. All machine
provenance/extern-static leaves retain their stateful failure behavior. -/
def queriesAt (prepared : Prepared) (site : Site) (machine : ConstantQueries P E K H) : ConstantQueries P E K H :=
  let evidence := (prepared.evidence.filter (·.site == site)).map (·.query)
  { machine with
    instantiateAndNormalize := fun fnInstance original =>
      match normalizationFromEvidence evidence fnInstance original with
      | .ok value => pure value
      | .error error => throw error
    evaluate := fun fnInstance normalized span =>
      match evaluationFromEvidence evidence fnInstance normalized span with
      | .ok value => pure value
      | .error error => throw error }

end Miri.Input.CompilerConstantQueries
