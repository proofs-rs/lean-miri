import Miri.Input.CompilerGlobals
import Miri.Input.LowerMIR
import Miri.Input.CompilerInstance
import Miri.Input.RuntimeArrayQueries
import Miri.Input.CallCompatibility
import Miri.Input.CompilerWorldCompatibility
import Miri.ABI.FnAbi
import Miri.Interpreter.Call

/-! Internal reuse of actual rustc instance-resolution and FnAbi query results.
Complete instance arguments and shared definition/type-constant tables are kept.
Missing/ambiguous/conflicting queries remain errors. This is not a compiler
instance solver or Miri's foreign-function/shim dispatcher. -/
namespace Miri.Input.CallResolution
open Lean Miri.ABI Miri.Interpreter
abbrev Result := Except String
private def require (value : Option A) (message : String) : Result A :=
  match value with | some value => pure value | none => throw message

def convention (source : CanonicalAbi) : Result CanonAbi := do
  match source.kind with
  | .c => pure .C | .rust => pure .Rust | .rustCold => pure .RustCold
  | .rustPreserveNone => pure .RustPreserveNone | .rustTail => pure .RustTail
  | .custom => pure .Custom | .swift => pure .Swift | .gpuKernel => pure .GpuKernel
  | .arm =>
    let call ← require source.armCall "missing Arm calling convention"
    return .Arm (← match call with
      | .aapcs => pure ArmCall.Aapcs | .cmseNonSecureCall => pure .CCmseNonSecureCall
      | .cmseNonSecureEntry => pure .CCmseNonSecureEntry)
  | .interrupt =>
    let kind ← require source.interruptKind "missing interrupt calling convention"
    return .Interrupt (← match kind with
      | .avr => pure InterruptKind.Avr | .avrNonBlocking => pure .AvrNonBlocking
      | .msp430 => pure .Msp430 | .riscvMachine => pure .RiscvMachine
      | .riscvSupervisor => pure .RiscvSupervisor | .x86 => pure .X86)
  | .x86 =>
    let call ← require source.x86Call "missing x86 calling convention"
    return .X86 (← match call with
      | .fastcall => pure X86Call.Fastcall | .stdcall => pure .Stdcall | .sysv64 => pure .SysV64
      | .thiscall => pure .Thiscall | .vectorcall => pure .Vectorcall | .win64 => pure .Win64)

def functionAbi (runtime : RuntimeMetadata) (source : FunctionAbi) : Result (FnAbi TypeId) := do
  let args ← source.arguments.mapM fun argument => (CallCompatibility.argument runtime argument).mapError toString
  let ret ← (CallCompatibility.argument runtime source.returnValue).mapError toString
  if source.signatureSeed.isSome then throw "legacy source ABI signature seed is not a rustc result"
  let some fixedCount := source.residualFixedCount
    | throw "rustc FnAbi fixed_count result is absent"
  if fixedCount >= 2^32 then throw "FnAbi.fixed_count exceeds u32"
  if fixedCount > args.size then throw "FnAbi.fixed_count exceeds actual arguments"
  -- rustc's physical `FnAbi.args` can include the compiler-injected caller
  -- location while `fixed_count` counts only explicit source arguments.
  -- Preserve both exact facts here; demanded call initialization validates
  -- their relationship against the exact `requires_caller_location` query.
  return ⟨args,ret,source.cVariadic,UInt32.ofNat fixedCount,← convention source.callingConvention,source.unwindSeed.canUnwind⟩

/-- The input carries only an ABI table reference. Conversion to the semantic
ABI happens when an operation requests it; input graphs are never expanded. -/
def functionAbiId (runtime : RuntimeMetadata) (id : Nat) : Result (FnAbi TypeId) := do
  let source ← require runtime.source.functionAbis[id]? s!"compiler FnAbi ID {id} out of bounds"
  functionAbi runtime source


structure Site where
  bodyIndex : Nat
  block : MIR.BasicBlockId
  deriving DecidableEq, Repr
structure Resolution where
  callee : CallInstance
  sourceInstanceId : InstanceId
  function : MIR.Operand
  abi : CallAbiEvidence
  source : CallResolutionEvidence
structure Entry where
  site : Site
  outcome : Except String Resolution
structure InstanceBody where
  fnInstance : CallInstance
  sourceInstanceId : InstanceId
  bodyIndex : Nat
structure Indirect where
  site : Site
  function : MIR.Operand
  functionType : MIR.TyId
  abi : Option Nat
  source : CallResolutionEvidence
structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  entries : Array Entry
  bodies : Array InstanceBody
  obligations : Array Obligation
  indirect : Array Indirect := #[]

private def decodeResolution (instances : Array InstanceNode)
    (function : MIR.Operand) (source : CallResolutionEvidence) : Result Resolution := do
  let virtual := source.kind == .virtualDispatch
  unless source.kind == .direct || source.kind == .llvmIntrinsic || virtual do throw "callee is not a compiler instance dispatch"
  let callee ← require source.instanceId "missing compiler call instance ID"
  let calleeKind ← CompilerInstance.Material.kindOf instances callee
  let isLlvm := match calleeKind with | .LlvmIntrinsic _ => true | _ => false
  unless (source.kind == .llvmIntrinsic) == isLlvm do
    throw "LLVM call tag/canonical instance mismatch"
  match calleeKind with
  | .LlvmIntrinsic _ =>
    unless source.kind == .llvmIntrinsic && source.abi == .llvmIntrinsic do
      throw "LLVM intrinsic requires exact no-ABI evidence"
  | .Virtual _ slot =>
    unless virtual do throw "virtual instance lacks virtual-dispatch query tag"
    unless source.dispatchSlot == some slot do throw "virtual dispatch slot/instance mismatch"
  | _ => unless !virtual do throw "virtual dispatch query did not return a Virtual instance"
  unless source.kind == .llvmIntrinsic do
    match source.abi with
    | .normal _ => pure ()
    | .sourceSignature => throw "legacy source ABI call evidence is not a rustc result"
    | .llvmIntrinsic => throw "ordinary call lacks ABI evidence"
  pure ⟨callee,callee,function,source.abi,source⟩

/-- Resolution reads decoded canonical identities; existing IDs never move.
Query failures are retained per call site, without deleting the imported MIR. -/
private def prepareUsingRuntime (profile : Lean.Options) (program : LoweredProgram) (runtime : RuntimeMetadata) :
    Result Prepared := do
  let instances := program.input.instances
  let tables := program.compilerTables
  let mut bodies := #[]
  let mut obligations := #[]
  for (sourceId,index) in program.instances do
    match CompilerInstance.Material.source instances sourceId with
    | .error message => obligations := obligations.push ⟨s!"instance[{sourceId}]",message⟩
    | .ok _ => bodies := bodies.push ⟨sourceId,sourceId,index⟩
  let mut entries := #[]
  let mut indirect := #[]
  for index in [:program.bodyCount] do
    let metadata ← program.bodyMetadata index
    for (blockIndex,function) in metadata.callSites do
        let sourceResolution ← require (metadata.callEvidence[blockIndex]?).join "missing compiler call resolution"
        if sourceResolution.kind == .indirect then
          let result : Result (TypeId × Option FunctionAbiId) := do
            let typeId ← require sourceResolution.functionType "indirect function type is missing"
            let sourceType ← require program.input.types[typeId]? "indirect function type is missing"
            unless sourceType.shapeKind == TypeShapeKind.functionPointer do throw "indirect dispatch metadata is not a function-pointer type"
            let abi ← match sourceResolution.abi with
              | .normal abi => pure (some abi)
              | .sourceSignature => throw "legacy source FnPtr ABI evidence is not a rustc result"
              | .llvmIntrinsic => throw "indirect call cannot use LLVM no-ABI dispatch"
            pure (typeId,abi)
          match result with
          | .error message =>
            obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].indirect",message⟩
            entries := entries.push ⟨⟨index,blockIndex⟩,.error message⟩
          | .ok (ty,abi) => indirect := indirect.push ⟨⟨index,blockIndex⟩,function,ty,abi,sourceResolution⟩
          continue
        let outcome := decodeResolution instances function sourceResolution
        if let .error message := outcome then
          obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].resolution",message⟩
        entries := entries.push ⟨⟨index,blockIndex⟩,outcome⟩
  return {
    program := program.withCompilerTables tables
    runtime
    entries
    bodies
    obligations
    indirect }

/-- Prepare call-resolution tables using the already validated immutable
runtime metadata for this program's unchanged ImportDocument. Compiler tables
may grow during preparation, but `CompilerGlobals.prepareProgram` changes only
the lowered bundle and leaves that document untouched. -/
def prepareWithRuntimeProfiled (profile : Lean.Options) (runtime : RuntimeMetadata) (program : LoweredProgram) : Result Prepared := do
  let program := profileit "prepare.compiler_globals" profile fun _ => CompilerGlobals.prepareProgram program
  prepareUsingRuntime profile program runtime

/-- Prepare call-resolution tables using validated runtime metadata. -/
def prepareWithRuntime (runtime : RuntimeMetadata) (program : LoweredProgram) : Result Prepared :=
  prepareWithRuntimeProfiled {} runtime program

/-- Validate target metadata before preparing canonical call-site queries. -/
def prepare (program : LoweredProgram) : Result Prepared := do
  let program := CompilerGlobals.prepareProgram program
  let runtime ← (RuntimeMetadata.ofDocument program.input).mapError toString
  prepareUsingRuntime {} program runtime

private def liftWorld (result : Result A) : RuntimeArrayTypes.CompilerM A :=
  match result with | .ok value => pure value | .error message => throw message

/-- Residual body/ABI/site records belong to the original source prefix.
Constructed IDs must never alias a numeric row from an unrelated/truncated store. -/
private def sourcePrefixInstance (document : ImportDocument) (world : RuntimeArrayTypes.World)
    (callee : CallInstance) : Result Unit := do
  let .material actual ← world.instances.lookup callee
    | throw "source instance capability does not cover a constructed instance"
  let some source := document.instances[callee]?
    | throw "source instance capability identity is absent"
  let expected ← InstanceArena.Key.ofSource world.arena source.instanceKind source.genericArgs
  unless actual == expected do throw "source instance capability identity disagrees with current world"

def atSite (prepared : Prepared) (site : Site) : RuntimeArrayTypes.CompilerM Resolution := do
  let world ← get
  let view ← liftWorld (world.bodies.lookup site.bodyIndex)
  let matching : Array Entry := match view with
    | .material _ => prepared.entries.filter (·.site == site)
    | .constructed _ => #[]
  if !matching.isEmpty then
    unless matching.size == 1 do throw "missing or ambiguous compiler call site"
    let entry ← liftWorld (require matching[0]? "missing compiler call site")
    let resolution ← liftWorld entry.outcome
    liftWorld (sourcePrefixInstance prepared.program.input (← get) resolution.callee)
    return resolution
  throw "missing exact rustc call-site instance resolution"

/-- Function operand identity is checked in addition to body and block.
Source sites are compiler-table indices, never diagnostic span matches. -/
def resolveAt (prepared : Prepared) (site : Site) (function : MIR.Operand) : RuntimeArrayTypes.CompilerM CallInstance := do
  let found ← atSite prepared site
  if found.function != function then throw "call-site function operand mismatch"
  return found.callee

def abiOfInstance (prepared : Prepared) (world : RuntimeArrayTypes.World)
    (fnInstance : CallInstance) (extraArgs : Array TypeId) : Result (FnAbi TypeId) := do
  sourcePrefixInstance prepared.program.input world fnInstance
  -- The exporter records fn_abi_of_instance(..., List::empty()). Extra-vararg
  -- queries require additional compiler evidence, even if an ABI looks similar.
  if !extraArgs.isEmpty then throw "missing compiler FnAbi query for extra arguments"
  let mut found := none
  for entry in prepared.entries do
    if let .ok resolution := entry.outcome then
      if resolution.callee == fnInstance then
        let .normal id := resolution.abi | continue
        let abi ← functionAbiId prepared.runtime id
        if let some old := found then
          if old != abi then throw "conflicting compiler FnAbi queries for one complete instance"
        found := some abi
  require found "missing compiler FnAbi instance query"

/-- A loaded body carries the exact source table key. Equal MIR syntax does
not make distinct root/template/promoted/instance body identities interchangeable. -/
def loadedBodyOfInstance (prepared : Prepared) (fnInstance : CallInstance) : RuntimeArrayTypes.CompilerM LoadedBody := do
  let world ← get
  let view ← liftWorld (world.instances.lookup fnInstance)
  let bodyIndex ← match view with
    | .material _ => do
      liftWorld (sourcePrefixInstance prepared.program.input world fnInstance)
      let matching := prepared.bodies.filter (·.fnInstance == fnInstance)
      unless matching.size == 1 do
        throw s!"missing or ambiguous canonical instance body identity: requested={reprStr fnInstance}, matches={matching.size}"
      let some candidate := matching[0]? | throw "compiler instance body is unavailable"
      let source ← liftWorld (require prepared.program.input.instances[candidate.sourceInstanceId]?
        "canonical source instance record is missing")
      unless source.kind == .instanceMir do throw "compiler body is not a substituted executable instance"
      pure candidate.bodyIndex
    | .constructed _ => throw "constructed instance has no exact rustc body result"
  let identity := BodyIdentity.ofCanonicalIndex bodyIndex
  let body ← prepared.program.resolveBodyIdentity identity
  unless body.input.instanceId == fnInstance do throw "instance/body identity mismatch"
  unless body.obligations.isEmpty do throw "lowered instance body has unresolved obligations"
  return ⟨identity, body.body⟩

/-- Compatibility syntax-only view of the exact loaded body. It retains the
same unique-key and body ownership checks; equal bodies are not merged. -/
def bodyOfInstance (prepared : Prepared) (fnInstance : CallInstance) : RuntimeArrayTypes.CompilerM MIR.Body := do
  return (← loadedBodyOfInstance prepared fnInstance).body

private def lift (result : Result A) : CallM S A :=
  match result with | .ok value => pure value | .error message => throw (.unsupported message)

/-- Replace only ABI leaves with complete compiler records and source layout
compatibility. Machine dispatch, target features, caller locations, pointer
resolution and actual body interception remain required in the supplied hooks. -/
def bindAbi (prepared : Prepared) (types : RuntimeArrayQueries.Access S)
    (_compatibility : CallCompatibility.Evidence S)
    (budget : Nat)
    (base : CallHooks P S C E Other Extern (FnAbi TypeId) (ArgAbi TypeId)) :
    CallHooks P S C E Other Extern (FnAbi TypeId) (ArgAbi TypeId) := {
  base with
  instanceKind := fun inst => do lift (CompilerInstance.kindOf (← RuntimeArrayQueries.compilerSnapshot types) inst)
  instanceArgs := fun inst => do lift (CompilerInstance.argsOf (← RuntimeArrayQueries.compilerSnapshot types) inst)
  itemInstance := fun definition args => lift
    (CompilerInstance.Material.item prepared.program.input.instances definition args)
  fnAbiOfInstance := fun _ fnInstance extra => do lift (abiOfInstance prepared (← RuntimeArrayQueries.compilerSnapshot types) fnInstance extra)
  abiCanUnwind := FnAbi.canUnwind
  abiVariadic := FnAbi.cVariadic
  abiFixedCount := fun abi => abi.fixedCount.toNat
  abiArgs := FnAbi.args
  abiReturn := FnAbi.ret
  sameConvention := fun left right => left.conv == right.conv
  argLayout := ArgAbi.layout
  argIsIgnore := ArgAbi.isIgnore
  isOneZst := fun layout => layout.layout.is1zst
  checkArgumentCompat := fun _ caller callee =>
    LayoutCompat.checkArgumentCompat (CompilerWorldCompatibility.queries ⟨prepared.runtime,prepared.program,none⟩ types)
      budget caller callee }

end Miri.Input.CallResolution
