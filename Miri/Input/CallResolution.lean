import Miri.Input.RuntimeProgram
import Miri.Input.CompilerInstance
import Miri.Input.CallCompatibility
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
  if source.status != .supported then throw "calling-convention query is unsupported"
  match source.kind with
  | .c => pure .C | .rust => pure .Rust | .rustCold => pure .RustCold
  | .rustPreserveNone => pure .RustPreserveNone | .rustTail => pure .RustTail
  | .custom => pure .Custom | .swift => pure .Swift | .gpuKernel => pure .GpuKernel
  | .arm =>
    let call ← require source.armCall "missing Arm calling convention"
    return .Arm (← match call with
      | .aapcs => pure ArmCall.Aapcs | .cmseNonSecureCall => pure .CCmseNonSecureCall
      | .cmseNonSecureEntry => pure .CCmseNonSecureEntry | .unknown _ => throw "unknown Arm convention")
  | .interrupt =>
    let kind ← require source.interruptKind "missing interrupt calling convention"
    return .Interrupt (← match kind with
      | .avr => pure InterruptKind.Avr | .avrNonBlocking => pure .AvrNonBlocking
      | .msp430 => pure .Msp430 | .riscvMachine => pure .RiscvMachine
      | .riscvSupervisor => pure .RiscvSupervisor | .x86 => pure .X86
      | .unknown _ => throw "unknown interrupt convention")
  | .x86 =>
    let call ← require source.x86Call "missing x86 calling convention"
    return .X86 (← match call with
      | .fastcall => pure X86Call.Fastcall | .stdcall => pure .Stdcall | .sysv64 => pure .SysV64
      | .thiscall => pure .Thiscall | .vectorcall => pure .Vectorcall | .win64 => pure .Win64
      | .unknown _ => throw "unknown x86 convention")
  | .unknown _ => throw "unknown canonical ABI"

def functionAbi (runtime : RuntimeMetadata) (source : FunctionAbi) : Result (FnAbi TypeId) := do
  let args ← source.arguments.mapM fun argument => (CallCompatibility.argument runtime argument).mapError toString
  let ret ← (CallCompatibility.argument runtime source.returnValue).mapError toString
  if source.fixedCount >= 2^32 then throw "FnAbi.fixed_count exceeds u32"
  if source.fixedCount > args.size then throw "FnAbi.fixed_count exceeds actual arguments"
  -- rustc's physical `FnAbi.args` can include the compiler-injected caller
  -- location while `fixed_count` counts only explicit source arguments.
  -- Preserve both exact facts here; demanded call initialization validates
  -- their relationship against the exact `requires_caller_location` query.
  return ⟨args,ret,source.cVariadic,UInt32.ofNat source.fixedCount,← convention source.callingConvention,source.canUnwind⟩

private def functionAbiData (runtime : RuntimeMetadata) (source : FunctionAbiData) : Result (FnAbi TypeId) := do
  let tables := runtime.source.abiTables
  let argumentIds ← (tables.argumentLists.lookup source.arguments).mapError fun id => s!"invalid ABI argument list {id}"
  let argument := fun id => do
    let source ← (tables.arguments.lookup id).mapError fun id => s!"invalid ABI argument {id}"
    (CallCompatibility.argumentData runtime source).mapError toString
  let arguments ← argumentIds.mapM argument
  let result ← argument source.returnValue
  if source.fixedCount >= 2^32 || source.fixedCount > arguments.size then
    throw "function ABI fixed argument count is invalid"
  return ⟨arguments,result,source.cVariadic,UInt32.ofNat source.fixedCount,
    ← convention source.callingConvention,source.canUnwind⟩

def functionAbiById (runtime : RuntimeMetadata) (id : Nat) : Result (FnAbi TypeId) := do
  let source ← runtime.source.abiTables.functions.lookup id |>.mapError (fun id => s!"invalid function ABI ID {id}")
  functionAbiData runtime (← source)

private def buildFunctionAbiCache (runtime : RuntimeMetadata) :
    MIR.SharedTable (Except String (FnAbi TypeId)) :=
  runtime.source.abiTables.functions.map (fun entry => entry.map (fun source => source >>= functionAbiData runtime))

structure FunctionAbiCache (runtime : RuntimeMetadata) where
  private mk ::
  private entries : MIR.SharedTable (Except String (FnAbi TypeId))
  private exact : entries = buildFunctionAbiCache runtime

def prepareFunctionAbiCacheProfiled (profile : Lean.Options) (runtime : RuntimeMetadata) :
    FunctionAbiCache runtime :=
  ⟨profileit "prepare.function_abi_cache" profile (fun _ => buildFunctionAbiCache runtime), rfl⟩

def prepareFunctionAbiCache (runtime : RuntimeMetadata) : FunctionAbiCache runtime :=
  prepareFunctionAbiCacheProfiled {} runtime

def functionAbiId (runtime : RuntimeMetadata) (id : Nat)
    (cache : Option (FunctionAbiCache runtime)) : Result (FnAbi TypeId) := do
  let some cache := cache | throw "compiler ABI cache absent"
  let result ← cache.entries.lookup id |>.mapError (fun id => s!"invalid function ABI ID {id}")
  result

structure Site where
  bodyIndex : Nat
  block : MIR.BasicBlockId
  deriving DecidableEq, Repr
structure Resolution where
  callee : CallInstance
  sourceInstanceId : InstanceId
  function : MIR.OperandId
  abi : Except String (FnAbi TypeId)
  functionType : Except String TypeId
structure Entry where
  site : Site
  outcome : Except String Resolution
structure InstanceBody where
  fnInstance : CallInstance
  sourceInstanceId : InstanceId
  bodyIndex : Nat
structure Indirect where
  site : Site
  function : MIR.OperandId
  functionType : MIR.TyId
  abi : FnAbi TypeId
structure Prepared where
  owner : RuntimeProgram
  functionAbiCache : FunctionAbiCache owner.runtime
  /-- Strict source unit-layout scan cached as a deferred outcome for ABI
  compatibility calls. Manual records retain the linear compatibility path. -/
  unitLayoutCache : Option (CallCompatibility.UnitLayoutCache owner.runtime) := none
  entries : Array Entry
  bodies : Array InstanceBody
  obligations : Array Obligation
  indirect : Array Indirect := #[]

@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.owner.program
@[inline] def Prepared.runtime (prepared : Prepared) : RuntimeMetadata := prepared.owner.runtime

def Prepared.withProgram (prepared : Prepared) (program : LoweredProgram) : Prepared :=
  {prepared with owner := prepared.owner.withProgram program}

private def decodeResolution (runtime : RuntimeMetadata)
    (abiCache : FunctionAbiCache runtime) (abiId : Option Nat)
    (function : MIR.OperandId) (source : CallSiteData) :
    Result Resolution := do
  let status ← source.status
  let kind ← source.kind
  let virtual := kind == "virtual_dispatch"
  unless kind == "resolved_instance" || virtual do throw "callee is not a compiler instance dispatch"
  unless status == "supported" || (virtual && status == "unknown") do
    throw "compiler callee resolution is unavailable"
  let sourceInstanceId ← source.instanceId
  let callee ← runtime.source.mirTables.instance sourceInstanceId
  match callee.kind with
  | .Virtual _ slot =>
    unless virtual do throw "virtual instance lacks virtual-dispatch query tag"
    unless (← source.dispatchSlot) == slot do throw "virtual dispatch slot/instance mismatch"
  | _ => unless !virtual do throw "virtual dispatch query did not return a Virtual instance"
  let abi := do
    let id ← require abiId "missing call-site ABI reference"
    functionAbiId runtime id (some abiCache)
  return ⟨callee,sourceInstanceId,function,abi,source.functionType⟩


/-- Appended identities are rebound through all bodies; existing IDs never move.
Query failures are retained per call site, without deleting the imported MIR. -/
private def prepareUsingRuntime (profile : Lean.Options) (owner : RuntimeProgram) :
    Result Prepared := do
  let program := owner.program
  let runtime := owner.runtime
  let functionAbiCache := prepareFunctionAbiCacheProfiled profile runtime
  let mut bodies := #[]
  let mut obligations := #[]
  for (sourceId,index) in program.instances do
    match program.input.mirTables.instance sourceId with
    | .error message => obligations := obligations.push ⟨s!"instance[{sourceId}]",message⟩
    | .ok fnInstance =>
      bodies := bodies.push ⟨fnInstance,sourceId,index⟩
  let mut entries := #[]
  let mut indirect := #[]
  for (body,index) in program.bundle.bodies.toList.zipIdx do
    let metadata ← require program.input.mirTables.bodySources[index]? "body compiler metadata absent"
    for (blockId,blockIndex) in body.body.basicBlocks.toList.zipIdx do
      let block ← (program.input.mirTables.mir.blocks.lookup blockId.index).mapError (fun id => s!"invalid source block ID {id}")
      let terminator ← (program.input.mirTables.mir.terminators.lookup block.terminator.index).mapError (fun id => s!"invalid source terminator ID {id}")
      let function ← match terminator.kind with
        | .Call function .. | .TailCall function .. => pure (some function)
        | _ => pure none
      if let some function := function then
        let sourceResolution ← require metadata.calls[blockIndex]? "missing call-site metadata" >>= id
        let sourceResolution ← require sourceResolution "missing call-site resolution"
        if sourceResolution.kind.toOption == some "indirect_function_pointer" then
          let result := do
            unless (← sourceResolution.status) == "supported" do throw "indirect compiler signature/ABI query is unavailable"
            let typeId ← sourceResolution.functionType
            let sourceType ← require program.input.types[typeId]? "indirect function type is missing"
            unless sourceType.shapeKind == TypeShapeKind.functionPointer do throw "indirect dispatch metadata is not a function-pointer type"
            let sourceBlock ← require body.input.blocks[blockIndex]? "missing source block"
            let abiId ← require sourceBlock.callAbi "missing indirect ABI reference"
            pure (typeId,← functionAbiId runtime abiId (some functionAbiCache))
          match result with
          | .error message =>
            obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].indirect",message⟩
            entries := entries.push ⟨⟨index,blockIndex⟩,.error message⟩
          | .ok (ty,abi) =>
            indirect := indirect.push ⟨⟨index,blockIndex⟩,function,ty,abi⟩
          continue
        let result := do
          decodeResolution runtime functionAbiCache (body.input.blocks[blockIndex]?.bind (·.callAbi)) function sourceResolution
        let outcome ← match result with
          | .error message =>
            obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].resolution",message⟩
            pure (.error message)
          | .ok resolution =>
            if let .error message := resolution.abi then
              obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].fn_abi",message⟩
            pure (.ok resolution)
        entries := entries.push ⟨⟨index,blockIndex⟩,outcome⟩
  return {
    owner
    functionAbiCache
    unitLayoutCache := some (CallCompatibility.bindUnitLayout runtime)
    entries
    bodies
    obligations
    indirect }

/-- Runtime metadata and the lowered view have one compiler source owner. -/
def prepareOwnedProfiled (profile : Lean.Options) (owner : RuntimeProgram) : Result Prepared :=
  prepareUsingRuntime profile owner

def prepareOwned (owner : RuntimeProgram) : Result Prepared := prepareOwnedProfiled {} owner

def prepare (program : LoweredProgram) : Result Prepared := do
  prepareOwned (← RuntimeProgram.ofProgram program)

def atSite (prepared : Prepared) (site : Site) : Result Resolution := do
  let matching := prepared.entries.filter (·.site == site)
  if matching.size != 1 then throw "missing or ambiguous compiler call site"
  (← require matching[0]? "missing compiler call site").outcome

/-- Function operand identity is checked in addition to body and block.
Source sites are compiler-table indices, never diagnostic span matches. -/
def resolveAt (prepared : Prepared) (site : Site) (function : MIR.OperandId) : Result CallInstance := do
  let found ← atSite prepared site
  if found.function != function then throw "call-site function operand mismatch"
  return found.callee

def abiOfInstance (prepared : Prepared) (fnInstance : CallInstance) (extraArgs : Array TypeId) : Result (FnAbi TypeId) := do
  -- The exporter records fn_abi_of_instance(..., List::empty()). Extra-vararg
  -- queries require additional compiler evidence, even if an ABI looks similar.
  if !extraArgs.isEmpty then throw "missing compiler FnAbi query for extra arguments"
  let mut found := none
  for entry in prepared.entries do
    if let .ok resolution := entry.outcome then
      if resolution.callee == fnInstance then
        let abi ← resolution.abi
        if let some old := found then
          if old != abi then throw "conflicting compiler FnAbi queries for one complete instance"
        found := some abi
  require found "missing compiler FnAbi instance query"

/-- A loaded body carries the exact source table key. Equal MIR syntax does
not make distinct root/template/promoted/instance body identities interchangeable. -/
def loadedBodyOfInstance (prepared : Prepared) (fnInstance : CallInstance) : Result LoadedBody := do
  let matching := prepared.bodies.filter (·.fnInstance == fnInstance)
  unless matching.size == 1 do
    throw s!"missing or ambiguous canonical instance body identity: requested={reprStr fnInstance}, matches={matching.size}"
  let some candidate := matching[0]? | throw "compiler instance body is unavailable"
  let source ← prepared.program.input.instance candidate.sourceInstanceId
  unless source.kind == .instanceMir do throw "compiler body is not a substituted executable instance"
  let instantiated ← require source.bodyInstantiation "instance body lacks substitution evidence"
  unless instantiated.status == .supported && instantiated.tag == "substituted_and_normalized" do
    throw "instance body substitution/normalization is unresolved"
  unless source.instanceArgsAreMonomorphic == some true do throw "instance arguments are not known monomorphic"
  let body ← require prepared.program.bundle.bodies[candidate.bodyIndex]? "instance body index is absent"
  unless body.obligations.isEmpty do throw "lowered instance body has unresolved obligations"
  let id ← require prepared.program.input.mirTables.bodies[candidate.bodyIndex]? "instance MIR table body is absent"
  unless body.bodyId == id do throw "lowered instance body ID differs from canonical MIR table"
  let loaded ← LoadedBody.ofTables (.ofCanonicalIndex candidate.bodyIndex) prepared.program.input.mirTables.mir id
  unless loaded.body == body.body do throw "lowered instance body metadata differs from canonical MIR table"
  return loaded

private def lift (result : Result A) : CallM S A :=
  match result with | .ok value => pure value | .error message => throw (.unsupported message)

/-- Replace only ABI leaves with complete compiler records and source layout
compatibility. Machine dispatch, target features, caller locations, pointer
resolution and actual body interception remain required in the supplied hooks. -/
def bindAbi (prepared : Prepared) (compatibility : CallCompatibility.Evidence S)
    (budget : Nat)
    (base : CallHooks P S C E Other Extern (FnAbi TypeId) (ArgAbi TypeId)) :
    CallHooks P S C E Other Extern (FnAbi TypeId) (ArgAbi TypeId) := {
  base with
  fnAbiOfInstance := fun _ fnInstance extra => lift (abiOfInstance prepared fnInstance extra)
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
    LayoutCompat.checkArgumentCompat (CallCompatibility.queries prepared.runtime compatibility prepared.unitLayoutCache)
      budget caller callee }

/-- Successful loading retains the canonical table key and its checked contents. -/
theorem loadedBodyOfInstance_tables (prepared : Prepared) (fnInstance : CallInstance)
    (body : LoadedBody) (loaded : loadedBodyOfInstance prepared fnInstance = .ok body) :
    prepared.program.input.mirTables.body body.identity.index = .ok body.body ∧
    prepared.program.input.mirTables.bodyId body.identity.index = .ok body.bodyId ∧
    body.tables = prepared.program.input.mirTables.mir ∧
    body.body.alwaysLive.all
      (fun id => id > body.body.argumentCount && id < body.body.locals.size) = true := by
  unfold loadedBodyOfInstance at loaded
  simp only [require, LoadedBody.ofTables, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at loaded
  by_cases count : ((prepared.bodies.filter (·.fnInstance == fnInstance)).size == 1) = true
  · rw [ite_eq_left count] at loaded
    cases candidateEq : (prepared.bodies.filter (·.fnInstance == fnInstance))[0]? with
    | none => simp only [candidateEq] at loaded; contradiction
    | some candidate =>
      simp only [candidateEq] at loaded
      cases sourceEq : prepared.program.input.instance candidate.sourceInstanceId with
      | error reason => simp only [sourceEq] at loaded; contradiction
      | ok source =>
        simp only [sourceEq] at loaded
        by_cases kind : (source.kind == .instanceMir) = true
        · rw [ite_eq_left kind] at loaded
          cases instEq : source.bodyInstantiation with
          | none => simp only [instEq] at loaded; contradiction
          | some inst =>
            simp only [instEq] at loaded
            by_cases status : (inst.status == .supported && inst.tag == "substituted_and_normalized") = true
            · rw [ite_eq_left status] at loaded
              by_cases mono : (source.instanceArgsAreMonomorphic == some true) = true
              · rw [ite_eq_left mono] at loaded
                cases loweredEq : prepared.program.bundle.bodies[candidate.bodyIndex]? with
                | none => simp only [loweredEq] at loaded; contradiction
                | some lowered =>
                  simp only [loweredEq] at loaded
                  by_cases obligations : lowered.obligations.isEmpty = true
                  · rw [ite_eq_left obligations] at loaded
                    cases idEq : prepared.program.input.mirTables.bodies[candidate.bodyIndex]? with
                    | none => simp only [idEq] at loaded; contradiction
                    | some id =>
                      simp only [idEq] at loaded
                      by_cases idMatch : (lowered.bodyId == id) = true
                      · rw [ite_eq_left idMatch] at loaded
                        cases lookupEq : prepared.program.input.mirTables.mir.bodies.lookup id.index with
                        | error reason => simp only [lookupEq, Except.mapError] at loaded; contradiction
                        | ok node =>
                          simp only [lookupEq, Except.mapError] at loaded
                          by_cases valid : node.alwaysLive.all
                              (fun id => id > node.argumentCount && id < node.locals.size) = true
                          · by_cases same : (node == lowered.body) = true
                            · simp [valid, same, pure, Except.pure] at loaded
                              cases loaded
                              exact ⟨by simp [MIRInputTables.body, MIRInputTables.bodyId,
                                  BodyIdentity.ofCanonicalIndex, idEq, lookupEq, Except.mapError,
                                  bind, Except.bind, pure, Except.pure],
                                by simp [MIRInputTables.bodyId, BodyIdentity.ofCanonicalIndex,
                                  idEq, pure, Except.pure], rfl, valid⟩
                            · simp [valid, same, pure, Except.pure] at loaded
                          · simp [valid, pure, Except.pure] at loaded
                      · rw [ite_eq_right idMatch] at loaded; contradiction
                  · rw [ite_eq_right obligations] at loaded; contradiction
              · rw [ite_eq_right mono] at loaded; contradiction
            · rw [ite_eq_right status] at loaded; contradiction
        · rw [ite_eq_right kind] at loaded; contradiction
  · rw [ite_eq_right count] at loaded; contradiction

end Miri.Input.CallResolution
