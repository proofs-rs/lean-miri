import Lean.Util.Profile
import Miri.Input.CompilerInstance
import Miri.Input.NormalizationBody
import Miri.Input.TypedValueAccess
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

inductive PathElement where
  | field (name : String)
  | index (value : Nat)
  deriving Repr, DecidableEq
structure Site where
  bodyIndex : Nat
  location : MIR.Location
  path : Array PathElement
  deriving Repr, DecidableEq
structure Evidence where
  site : Site
  query : CompilerConstantEvidence
  sourceOperand : TypedValue
  normalizedOperand : TypedValue
structure Prepared where
  program : LoweredProgram
  evidence : Array Evidence
  obligations : Array Obligation

/-! A source compatibility check is deep over JSON. Production preparation
does it once, then carries this binding with the exact values it checked.
The private constructor and dependent indices prevent a caller from supplying
an arbitrary cached Boolean or reusing it for different metadata. -/
structure Binding (prepared : Prepared) (runtime : RuntimeMetadata) where
  private mk ::
  compatible : Bool
  correct : compatible = (runtime.source.raw == prepared.program.input.raw)

def bind (prepared : Prepared) (runtime : RuntimeMetadata)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Binding prepared runtime :=
  let compatible := RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality prepared.program.input.raw
  ⟨compatible, RuntimeMetadata.JsonReflexivity.matchesRightOr_eq sourceEquality prepared.program.input.raw⟩

private partial def constants (value : TypedValue) (path : Array PathElement := #[]) :
    Array (Array PathElement × TypedValue) :=
  if ((value.field "constant").bind TypedValue.tag).toOption == some "evaluated_const" then #[(path,value)]
  else match value with
  | .array values => (values.mapIdx fun index child => constants child (path.push (.index index))).flatten
  | value => match value.fields with
    | .ok fields => (fields.map fun (name,child) => constants child (path.push (.field name))).flatten
    | .error _ => #[]

private def lookupPath (value : TypedValue) (path : Array PathElement) : Except String TypedValue :=
  path.foldlM (fun value key => match key with
    | .field name => value.field name
    | .index index => do
      let values ← value.elements
      match values[index]? with
      | some child => pure child
      | none => throw "normalized query changed operand structural path") value

private def sourceConstants (bodyIndex : Nat) (body : BodyCore) : Array (Site × TypedValue) := Id.run do
  let mut found := #[]
  for block in body.blocks do
    for (statement, index) in block.statements.toList.zipIdx do
      for (path, value) in constants statement.envelope do
        found := found.push (⟨bodyIndex, ⟨block.id,index⟩, path⟩,value)
    for (path,value) in constants block.terminator.envelope do
      found := found.push (⟨bodyIndex, ⟨block.id,block.statements.size⟩,path⟩,value)
  pure found

private def normalizedOperand (body : BodyCore) (site : Site) : Except String TypedValue := do
  let some block := body.blocks.find? (·.id == site.location.block)
    | throw "normalized body is missing source basic block"
  let node ← if site.location.statementIndex == block.statements.size then pure block.terminator
    else match block.statements[site.location.statementIndex]? with
      | some statement => pure statement
      | none => throw "normalized body is missing source statement"
  lookupPath node.envelope site.path

private def evidenceAt (ctx : LowerContext) (tables : CompilerTables) (fnInstance : CallInstance)
    (site : Site) (original normalized : TypedValue) : Except String (Evidence × CompilerTables) := do
  unless (← (← original.field "span").natural) == (← (← normalized.field "span").natural) do throw "normalization changed constant source span"
  let (source,tables) ← lowerCompilerConstOperand ctx tables original
  let (normal,tables) ← lowerCompilerConstOperand ctx tables normalized
  let evaluated ← normalized.field "constant"
  let ty ← (← normalized.field "type").natural
  let value ← lowerCompilerConstValue ctx ty (← evaluated.field "value")
  pure (⟨site, ⟨fnInstance,source.value,normal.value,normal.span,value⟩, original, normalized⟩,
    tables)

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
