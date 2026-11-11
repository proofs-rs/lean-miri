import Miri.Input.MIRLeaves

namespace Miri.Input.DecodeMIR
open Miri.MIR
abbrev Result := Except String

structure Context where
  typeCount : Nat
  allocationCount : Nat
  definitionCount : Nat
  typeConstantCount : Nat
  spanCount : Nat
  scalarSize : Nat → Option Nat := fun _ => none
  localCount : Nat := 0
  blockCount : Nat := 0
  scopeCount : Nat := 0

/-- Only numeric bounds survive parsing until the document tables are known.
There is no second MIR tree and validation never rebuilds MIR constructors. -/
structure References where
  types : Option Nat := none
  allocations : Option Nat := none
  definitions : Option Nat := none
  typeConstants : Option Nat := none
  spans : Option Nat := none
  scalarWidths : Array (Nat × Nat) := #[]

structure ParsedBody where
  value : Body
  references : References

structure ParsedOperand where
  value : MIR.Operand
  typeId : Option Nat
instance : Coe ParsedOperand MIR.Operand := ⟨(·.value)⟩

structure ParsedBlock where
  value : MIR.BasicBlock
  facts : Array NodeFacts
  evidence : Option CallResolutionEvidence

private def check (id count : Nat) (what : String) : Result Unit := do
  unless id < count do throw s!"unresolved {what} {id}"
private def checkBound (id : Option Nat) (count : Nat) (what : String) : Result Unit := do
  for id in id do check id count what

def resolveConstValue (ctx : Context) (ty : Nat) (value : MIR.ConstValue) : Result MIR.ConstValue := do
  check ty ctx.typeCount "type"
  match value with
  | .Scalar (.Int _ size) =>
    let some expected := ctx.scalarSize ty | throw s!"missing scalar byte width for type {ty}"
    unless size == expected do throw s!"scalar byte width disagrees with type {ty}"
  | .Scalar (.Ptr (.Allocation id _ _ _)) | .Slice id _ | .Indirect id _ =>
    check id ctx.allocationCount "allocation"
  | _ => pure ()
  pure value

def validateReferences (ctx : Context) (refs : References) : Result Unit := do
  checkBound refs.types ctx.typeCount "type"
  checkBound refs.allocations ctx.allocationCount "allocation"
  checkBound refs.definitions ctx.definitionCount "definition"
  checkBound refs.typeConstants ctx.typeConstantCount "type constant"
  checkBound refs.spans ctx.spanCount "source span"
  for (ty, size) in refs.scalarWidths do
    let some expected := ctx.scalarSize ty | throw s!"missing scalar byte width for type {ty}"
    unless size == expected do throw s!"scalar byte width disagrees with type {ty}"

def resolveBody (ctx : Context) (body : ParsedBody) : Result Body := do
  validateReferences ctx body.references
  pure body.value

namespace MIRParser
structure State where
  references : References := {}
  facts : NodeFacts := {}
  locals : Option Nat := none
  blocks : Option Nat := none
  scopes : Option Nat := none

abbrev Parser := StateT State JsonReader.Parser

private def extend (previous : Option Nat) (id : Nat) : Option Nat :=
  some (previous.map (max id) |>.getD id)

def recordType (id : Nat) : Parser Unit := modify fun s =>
  {s with references.types := extend s.references.types id}
def recordDef (id : Nat) : Parser Unit := modify fun s =>
  {s with references.definitions := extend s.references.definitions id}
def recordSpan (id : Nat) : Parser Unit := modify fun s =>
  {s with references.spans := extend s.references.spans id}
def recordAllocation (id : Nat) : Parser Unit := modify fun s =>
  {s with references.allocations := extend s.references.allocations id}
def recordTypeConstant (id : Nat) : Parser Unit := modify fun s =>
  {s with references.typeConstants := extend s.references.typeConstants id}
def recordLocal (id : Nat) : Parser Unit := modify fun s =>
  {s with locals := extend s.locals id}
def recordBlock (id : Nat) : Parser Unit := modify fun s =>
  {s with blocks := extend s.blocks id}
def recordScope (id : Nat) : Parser Unit := modify fun s =>
  {s with scopes := extend s.scopes id}

def object (initial : σ) (step : σ → String → Parser σ) : Parser σ :=
  fun state => JsonReader.object (initial, state) fun (value, state) key => (step value key).run state

private def rawAny : JsonReader.Parser Char := Std.Internal.Parsec.any
private def rawPeek : JsonReader.Parser Char := Std.Internal.Parsec.peek!
private def rawSkip : JsonReader.Parser Unit := Std.Internal.Parsec.skip

private partial def arrayItems (parser : Parser α) (values : Array α) : Parser (Array α) := do
  let value ← parser
  Std.Internal.Parsec.String.ws
  match ← rawAny with
  | ']' => pure (values.push value)
  | ',' => Std.Internal.Parsec.String.ws; arrayItems parser (values.push value)
  | _ => JsonReader.fail "expected ',' or ']'"
def array (parser : Parser α) : Parser (Array α) := do
  Std.Internal.Parsec.String.skipChar '['
  Std.Internal.Parsec.String.ws
  if (← rawPeek) == ']' then rawSkip; pure #[]
  else arrayItems parser #[]

def nullable (parser : Parser α) : Parser (Option α) := do
  if (← rawPeek) == 'n' then
    Std.Internal.Parsec.String.skipString "null"; pure none
  else some <$> parser

def recordSource (source : MIR.SourceInfo) : Parser Unit := do
  recordSpan source.span.id
  recordScope source.scope

def recordRegion (region : MIR.Region) : Parser Unit := do
  let bound (b : MIR.BoundRegionKind) : Parser Unit := do
    match b with
    | .Named id => recordDef id
    | _ => pure ()
  match region with
  | .Bound _ _ b | .Placeholder _ _ b => bound b
  | .LateParameter id b =>
    recordDef id
    match b with
    | .Named id => recordDef id
    | _ => pure ()
  | _ => pure ()
def recordArgs (args : Array MIR.GenericArg) : Parser Unit := do
  for arg in args do
    match arg with
    | .Type id => recordType id
    | .Const id => recordTypeConstant id
    | .Lifetime r => recordRegion r

def recordAggregate (kind : MIR.AggregateKind) : Parser Unit := do
  match kind with
  | .Array ty | .RawPtr ty _ => recordType ty
  | .Tuple => pure ()
  | .Adt d _ args _ _ | .Closure d args | .Coroutine d args | .CoroutineClosure d args =>
    recordDef d; recordArgs args

def parsedPlace : Parser ParsedPlace := do
  let p ← place
  recordLocal p.value.localId
  recordType p.typeId
  for ty in p.projectionTypes do recordType ty
  for projection in p.value.projection do
    match projection with
    | .Field _ ty | .OpaqueCast ty | .UnwrapUnsafeBinder ty => recordType ty
    | .Index id => recordLocal id
    | _ => pure ()
  modify fun s => {s with facts.places := s.facts.places.push ⟨p.value, p.typeId, p.projectionTypes⟩}
  pure p

def makeConstant (ty : Nat) (span : MIR.SpanRef) (userType : Option Nat)
    (value : MIR.ConstValue) : Parser MIR.ConstOperand := do
  recordType ty
  recordSpan span.id
  match value with
  | .Scalar (.Int _ size) => modify fun s =>
    {s with references.scalarWidths := s.references.scalarWidths.push (ty, size)}
  | .Scalar (.Ptr (.Allocation id _ _ _)) | .Slice id _ | .Indirect id _ =>
    recordAllocation id
    modify fun s => {s with facts.constantAllocations := s.facts.constantAllocations.push id}
  | _ => pure ()
  pure ⟨span, userType, .Val value ty⟩

def constantType (constant : MIR.ConstOperand) : Option Nat :=
  match constant.value with
  | .Val _ ty => some ty

private def unwindTargets : MIR.UnwindAction → Array Nat
  | .Cleanup target => #[target]
  | .Continue | .Unreachable | .Terminate _ => #[]
def recordTargets (kind : MIR.TerminatorKind) : Parser Unit := do
  let targets : Array Nat := match kind with
    | .Goto target _ => #[target]
    | .SwitchInt _ targets => targets.cases.map (fun (.Case _ target) => target) ++ #[targets.otherwise]
    | .Drop _ target unwind _ asyncDrop => #[target] ++ unwindTargets unwind ++ asyncDrop.toArray
    | .Call _ _ _ target unwind _ _ => target.toArray ++ unwindTargets unwind
    | .Assert _ _ _ target unwind => #[target] ++ unwindTargets unwind
    | .Yield _ resume _ drop => #[resume] ++ drop.toArray
    | .FalseEdge real imaginary => #[real, imaginary]
    | .FalseUnwind real unwind => #[real] ++ unwindTargets unwind
    | .InlineAsm asm => asm.targets ++ unwindTargets asm.unwind
    | .UnwindResume | .UnwindTerminate _ | .Return | .Unreachable | .TailCall .. | .CoroutineDrop => #[]
  for target in targets do recordBlock target

def validateLocalBounds (locals blocks scopes : Nat) : Parser Unit := do
  let state ← get
  JsonReader.liftExcept do
    checkBound state.locals locals "local"
    checkBound state.blocks blocks "control-flow target"
    checkBound state.scopes scopes "source scope"
/-- Standalone parser entry point for a context whose bounds are already known. -/
def checked (ctx : Context) (parser : Parser α) : JsonReader.Parser α := do
  let (value, state) ← parser.run {}
  JsonReader.liftExcept (validateReferences ctx state.references)
  JsonReader.liftExcept do
    checkBound state.locals ctx.localCount "local"
    checkBound state.blocks ctx.blockCount "control-flow target"
    checkBound state.scopes ctx.scopeCount "source scope"
  pure value
end MIRParser

end Miri.Input.DecodeMIR
