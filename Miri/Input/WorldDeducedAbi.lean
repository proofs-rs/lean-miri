import Miri.MIR.Syntax
import Miri.Input.SourceMir
import Miri.Input.TermAutoTraits

/-! Pinned deduce_param_attrs.rs syntax visitor. Analysis follows optimized
source MIR and does not consume copied trait/drop/ABI answers. -/
namespace Miri.Input.WorldDeducedAbi
open Miri.MIR
abbrev Summary := Array UInt8

def mark (usage : Summary) (place : Place) (flags : UInt8) : Summary :=
  if place.projection[0]? == some .Deref then usage
  else if h : place.localId < usage.size then
    usage.set place.localId (usage[place.localId] ||| flags)
  else usage

def rvalue (usage : Summary) : Rvalue → Summary
  | .Ref _ .Shared place => mark usage place 10
  | .Ref _ (.Mut _) place => mark usage place 12
  | .RawPtr .Mut place | .RawPtr .Const place => mark usage place 12
  | .Reborrow _ .Not place => mark usage place 10
  | .Reborrow _ .Mut place => mark usage place 12
  | _ => usage

def statement (usage : Summary) : StatementKind → Summary
  | .Assign destination value => rvalue (mark usage destination 4) value
  | .SetDiscriminant place _ => mark usage place 4
  | _ => usage

def callArgument (usage : Summary) (arg : SpannedOperand) : Summary :=
  match arg.operand with | .Move place => mark usage place 12 | _ => usage

def asmOperand (usage : Summary) : InlineAsmOperand → Summary
  | .Out _ _ (some place) | .InOut _ _ _ (some place) => mark usage place 4
  | _ => usage

def terminator (usage : Summary) : TerminatorKind → Summary
  | .Drop place .. => mark usage place (if place.projection.isEmpty then 1 else 12)
  | .Call _ args destination .. => mark (args.foldl callArgument usage) destination 12
  | .TailCall .. => usage.map (· ||| 12)
  | .Yield _ _ resumeArgument _ => mark usage resumeArgument 12
  | .InlineAsm asm => asm.operands.foldl asmOperand usage
  | _ => usage

def analyze (body : Miri.MIR.Body) : Except String Summary := do
  unless body.phase == .Runtime .Optimized do throw "deduced attrs require exact optimized MIR source"
  if body.spreadArgument.isSome then throw "deduced attrs spread argument unsupported"
  let mut usage := #[(4 : UInt8)] ++ Array.replicate body.argumentCount 0
  for block in body.basicBlocks do
    usage := block.statements.foldl (fun state item => statement state item.kind) usage
    usage := terminator usage block.terminator.kind
  pure usage

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

mutual
/-- Empty-component branch of pinned ty/util.rs::needs_drop_components.
`false` means that the remaining needs_drop query is unsupported, never that
the type needs drop. Array length need not be evaluated when its element has
no drop components. The source grammar deliberately leaves ADTs unresolved. -/
def sourceNoDrop : Nat → GenericSubstitution.Term → Except String Bool
  | 0,_ => throw "ABI source needsDrop analysis exhausted"
  | fuel+1,term => do
    match term with
    | .atom .type tag payload =>
      match tag with
      | "bool" | "char" | "str" | "never" => pure (payload == "")
      | "int" => pure (#["i8","i16","i32","i64","i128","isize"].contains payload)
      | "uint" => pure (#["u8","u16","u32","u64","u128","usize"].contains payload)
      | "float" => pure (#["f16","f32","f64","f128"].contains payload)
      | _ => pure false
    | .node .type "raw_pointer" mutability (.cons child .nil) =>
      pure ((mutability == "mutable" || mutability == "immutable") && child.sort == .type)
    | .node .type "reference" mutability (.cons region (.cons child .nil)) =>
      pure ((mutability == "mutable" || mutability == "immutable") &&
        region.sort == .region && child.sort == .type)
    | .definition .type "function_definition" _
        (.cons (.binder _ (.node .aggregate "arguments" "" _)) .nil) => pure true
    | .node .type "function_pointer" "" (.cons binder .nil) =>
      let _ ← RawFunctionSignature.read binder
      pure true
    | .node .type "array" "" (.cons child (.cons length .nil)) =>
      unless child.sort == .type && length.sort == .constant do
        throw "ABI source needsDrop array has malformed sorts"
      sourceNoDrop fuel child
    | .node .type "tuple" "" children => sourceNoDropFields fuel children
    | _ => pure false
private def sourceNoDropFields : Nat → GenericSubstitution.Terms → Except String Bool
  | 0,_ => throw "ABI source needsDrop tuple analysis exhausted"
  | _+1,.nil => pure true
  | fuel+1,.cons child tail => do
    unless ← sourceNoDrop fuel child do return false
    sourceNoDropFields fuel tail
end

/-- Resolve the unique ordinary runtime source through the execution BodyArena.
No absent MIR record is interpreted as an empty upstream deduction. -/
def sourceBody (instanceId : InstanceId) : RuntimeArrayTypes.CompilerM Miri.MIR.Body := do
  let world ← get
  let view ← liftPure (world.instances.lookup instanceId)
  let key := match view with | .material key | .constructed key => key
  let mut found := none
  for (source,index) in world.metadata.source.mirTemplates.zipIdx do
    if source.sourceRole == .runtime && source.sourcePromoted.isNone &&
        (← liftPure (world.arena.identity source.definitionId)) == key.definition then
      unless found.isNone do throw "ambiguous raw optimized MIR for ABI deduction"
      found := some index
  if let some index := found then
    let id ← RuntimeArrayTypes.internBody index instanceId none
    return (← SourceMir.resolveBodyIdentity (.ofCanonicalIndex id)).mir
  if let .constructed _ := view then
    throw "constructed ABI deduction requires a raw optimized MIR template"
  let mut material := none
  for (seed,index) in world.metadata.source.bodies.zipIdx do
    let runtimeSource := match seed with
      | .material body => body.sourceRole == .runtime
      | .copyTemplate reference => (world.metadata.source.mirTemplates[reference.templateId]?).any
          (·.sourceRole == .runtime)
      | _ => false
    if runtimeSource && seed.instanceId == instanceId then
      unless material.isNone do throw "ambiguous material optimized MIR for ABI deduction"
      material := some index
  let some index := material | throw "raw optimized MIR for ABI deduction is absent"
  pure (← SourceMir.resolveBodyIdentity (.ofCanonicalIndex index)).mir

def applyUsage (usage : UInt8) (arg : Miri.ABI.ArgAbi TypeId) :
    RuntimeArrayTypes.CompilerM (Miri.ABI.ArgAbi TypeId) := do
  let .Indirect attrs space mode := arg.mode | return arg
  let readonly := usage &&& 4 == 0
  let capturesNone := usage &&& 8 == 0
  if usage &&& 1 != 0 && (readonly || capturesNone) then
    let term ← liftPure (GenericInstantiationWorld.ofType (← get).arena 16384 arg.layout.ty)
    unless ← liftPure (sourceNoDrop 16384 term) do
      throw "ABI deduction DROP requires source-derived needsDrop beyond the empty-component grammar"
  if readonly && usage &&& 2 != 0 then
    let term ← liftPure (GenericInstantiationWorld.ofType (← get).arena 16384 arg.layout.ty)
    unless ← liftPure (TermAutoTraits.trivial 16384 term) do
      throw "ABI deduction shared borrow requires source-derived Freeze"
  let bits : UInt8 := (if readonly then 32 else 0) ||| (if capturesNone then 1 else 0)
  let attrs := {attrs with regular := attrs.regular ||| bits.toUInt16}
  pure {arg with mode := .Indirect attrs space mode}

def adjust (instanceId : InstanceId) (session : AbiSessionMaterial)
    (policy : FunctionAbiMaterial) (args : Array (Miri.ABI.ArgAbi TypeId))
    (ret : Miri.ABI.ArgAbi TypeId) :
    RuntimeArrayTypes.CompilerM (Array (Miri.ABI.ArgAbi TypeId) × Miri.ABI.ArgAbi TypeId) := do
  unless (args.push ret).any (fun arg => match arg.mode with | .Indirect .. => true | _ => false) do
    return (args,ret)
  let world ← get
  let view ← liftPure (world.instances.lookup instanceId)
  let key := match view with | .material key | .constructed key => key
  -- Extern deduced_param_attrs comes from dependency metadata, computed under
  -- that crate's options. Current-session guards cannot reconstruct it.
  unless key.definition.crateIndex == 0 do
    throw "external Item indirect ABI requires original-crate deduction policy"
  if session.optimization == .no || session.incrementalEnabled || policy.alwaysComptime then
    return (args,ret)
  if world.metadata.source.producer.freezeLangItem.isNone then return (args,ret)
  let body ← sourceBody instanceId
  unless body.phase == .Runtime .Optimized do
    throw "deduced attrs require exact optimized MIR source"
  if body.spreadArgument.isSome then return (args,ret)
  let usage ← liftPure (analyze body)
  unless usage.size == args.size + 1 do throw "ABI deduction MIR/signature argument count differs"
  let some retUsage := usage[0]? | throw "ABI deduction return usage is absent"
  let ret ← applyUsage retUsage ret
  let args ← args.zipIdx.mapM fun (arg,index) => do
    let some argUsage := usage[index+1]? | throw "ABI deduction argument usage is absent"
    applyUsage argUsage arg
  pure (args,ret)

end Miri.Input.WorldDeducedAbi
