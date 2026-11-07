import Miri.Input.CompilerPanicFacts
import Miri.Input.CompilerLifecyclePipeline
import Miri.Input.CompilerFunctionFacts
import Miri.Input.CompilerExecutionFacts
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerNamedGlobals
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.CompilerThreadLocal
import Miri.Input.RuntimeArrayQueries
import Miri.Input.CompilerMain
import Miri.Input.CompilerContextSpan
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerExternStatic
import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.CompilerQueryIndices

/-! One compilation-local provider assembly. Source queries are the pinned
step.rs/call.rs/operand.rs/stack.rs/traits.rs query sites documented by the
constituent adapters. Preparation is ordered state threading, not independent
local ID allocation followed by merging. Every earlier view is rebound to the
final tables; source failures remain failures, not execution-readiness claims.
-/
namespace Miri.Input.CompilerProviders
open Lean Miri.ABI Miri.Memory Miri.Interpreter
structure Prepared where
  owner : RuntimeProgram
  lifecycle : CompilerLifecyclePipeline.Prepared
  functions : CompilerFunctionFacts.Prepared
  main : CompilerMain.Prepared
  intrinsics : CompilerIntrinsicFacts.Prepared
  constants : CompilerConstantQueries.Prepared
  namedConstants : CompilerNamedConstants.Prepared
  namedGlobals : CompilerNamedGlobals.Prepared
  externStatics : CompilerExternStatic.Prepared
  pointers : CompilerFunctionPointers.Prepared
  vtables : CompilerVTableMachine.Prepared
  namedAbi : CompilerNamedShimAbi.Prepared
  /-- Immutable compiler export table. Errors remain stored so source
  consumers retain their original demand-local failure boundary. -/
  foreignSymbols : Except String CompilerForeignSymbolTables.Prepared
  /-- Source-ordered exact lookup index. Global row parse errors remain stored
  and are reported only when a non-reflexive covariance query is demanded. -/
  covarianceIndex : CompilerQueryIndices.Covariance owner.input.covarianceQueries
  /-- Parsed helper-signature keys and exact duplicate rows, retaining the
  first malformed source row for demand-time error ordering. -/
  signatureAbiIndex : CompilerQueryIndices.SignatureAbi owner.runtime
  /-- Initial persistent interner. Runtime execution must thread its updated World. -/
  initialArrays : Except String RuntimeArrayTypes.World
  tls : Except String (Array CompilerThreadLocal.Entry)

@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.owner.program
@[inline] def Prepared.runtime (prepared : Prepared) : RuntimeMetadata := prepared.owner.runtime

/-- Demand the exact primitive identity from the typed compiler catalog. -/
def Prepared.primitiveLayout (p : Prepared) (key : String) :
    Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.primitiveLayout p.runtime key

def Prepared.orderingLayout (p : Prepared) : Except String (TyAndLayout TypeId) :=
  CompilerPrimitiveFacts.orderingLayout p.runtime

def Prepared.callerLocationType (p : Prepared) : Except String TypeId :=
  CompilerPrimitiveFacts.callerLocationType p.runtime

/-- Check index preservation at each append stage, including exact source spans.
No table contents may be normalized, reordered or silently replaced. -/
private def extension (old fresh : CompilerTables) : Except String Unit := do
  unless fresh.spans.size ≥ old.spans.size && fresh.spans.extract 0 old.spans.size == old.spans do
    throw "compiler provider preparation changed existing span identities"
  unless fresh.definitions.size ≥ old.definitions.size && fresh.definitions.extract 0 old.definitions.size == old.definitions do
    throw "compiler provider preparation changed existing definition identities"
  unless fresh.typeConstants.size ≥ old.typeConstants.size && fresh.typeConstants.extract 0 old.typeConstants.size == old.typeConstants do
    throw "compiler provider preparation changed existing type-constant identities"

private def rebindCalls (p : CompilerCallPipeline.Prepared) (program : LoweredProgram) : CompilerCallPipeline.Prepared :=
  {p with calls := p.calls.withProgram program
          scopes := {p.scopes with program}
          runtime := {p.runtime with program}
          symbols := {p.symbols with facts := {p.symbols.facts with
            context := p.symbols.facts.context.withProgram program}}}
private def rebindLifecycle (p : CompilerLifecyclePipeline.Prepared) (program : LoweredProgram) : CompilerLifecyclePipeline.Prepared :=
  let calls := rebindCalls p.calls program
  {p with calls
          instances := {p.instances with program}
          lifecycle := {p.lifecycle with program}
          backtrace := {p.backtrace with program}
          frames := {p.frames with calls}}

/-- All identity-appending adapters run on the immediately preceding program.
Predicate tokens are established exactly once by CompilerCallPipeline's shared
FactAdapters preparation, then consumed by vtable adapters without re-interning.
-/
def prepareProfiled (profile : Lean.Options) (input : LoweredProgram) : Except String Prepared := do
  let input ← profileit "preparation.providers.panic_facts" profile fun _ => CompilerPanicFacts.prepareProgram input
  -- The reader records declaration presence separately from a successful
  -- span lookup, so an explicitly declared null span cannot bypass its query.
  let seeded ← profileit "preparation.providers.context_span" profile fun _ => do
    if input.input.rootSpanDeclared then
      CompilerContextSpan.prepare input
    else pure input
  let calls ← profileit "preparation.providers.call_pipeline" profile fun _ =>
    CompilerCallPipeline.prepareProfiled profile seeded
  profileit "preparation.providers.extension_after_calls" profile fun _ =>
    extension input.compilerTables calls.calls.program.compilerTables
  let lifecycle ← profileit "preparation.providers.lifecycle" profile fun _ =>
    CompilerLifecyclePipeline.prepareProfiled profile calls
  let program := lifecycle.backtrace.program
  profileit "preparation.providers.extension_after_lifecycle" profile fun _ =>
    extension calls.calls.program.compilerTables program.compilerTables
  let owner := lifecycle.calls.calls.owner.withProgram program
  let runtime := owner.runtime
  let abiCache := some lifecycle.calls.calls.functionAbiCache
  let functions ← profileit "preparation.providers.function_facts" profile fun _ =>
    CompilerFunctionFacts.prepare owner abiCache
  profileit "preparation.providers.extension_after_functions" profile fun _ =>
    extension program.compilerTables functions.program.compilerTables
  let main ← profileit "preparation.providers.main" profile fun _ =>
    CompilerMain.prepare (owner.withProgram functions.program)
  profileit "preparation.providers.extension_after_main" profile fun _ =>
    extension functions.program.compilerTables main.program.compilerTables
  let intrinsics ← profileit "preparation.providers.intrinsics" profile fun _ => CompilerIntrinsicFacts.prepare (lifecycle.calls.symbols.facts.context.withProgram main.program)
  profileit "preparation.providers.extension_after_intrinsics" profile fun _ =>
    extension main.program.compilerTables intrinsics.program.compilerTables
  let constants ← profileit "preparation.providers.constants" profile fun _ =>
    CompilerConstantQueries.prepareProfiled profile (owner.withProgram intrinsics.program)
  profileit "preparation.providers.extension_after_constants" profile fun _ =>
    extension intrinsics.program.compilerTables constants.program.compilerTables
  let namedConstants ← profileit "preparation.providers.named_constants" profile fun _ =>
    CompilerNamedConstants.prepare (owner.withProgram constants.program)
  profileit "preparation.providers.extension_after_named_constants" profile fun _ =>
    extension constants.program.compilerTables namedConstants.program.compilerTables
  let namedGlobals ← profileit "preparation.providers.named_globals" profile fun _ =>
    CompilerNamedGlobals.prepare (owner.withProgram namedConstants.program)
  profileit "preparation.providers.extension_after_named_globals" profile fun _ =>
    extension namedConstants.program.compilerTables namedGlobals.program.compilerTables
  let externStatics ← profileit "preparation.providers.extern_statics" profile fun _ =>
    CompilerExternStatic.prepare (owner.withProgram namedGlobals.program)
  profileit "preparation.providers.extension_after_extern_statics" profile fun _ =>
    extension namedGlobals.program.compilerTables externStatics.program.compilerTables
  let owner := owner.withProgram externStatics.program
  let program := owner.program
  let lifecycle := profileit "preparation.providers.rebind_lifecycle" profile fun _ => rebindLifecycle lifecycle program
  let pointers ← profileit "preparation.providers.function_pointers" profile fun _ => CompilerFunctionPointers.prepare lifecycle.calls
  let vtables ← profileit "preparation.providers.vtable_machine" profile fun _ => CompilerVTableMachine.prepare lifecycle.calls
  let namedAbi ← profileit "preparation.providers.named_shim_abi" profile fun _ => CompilerNamedShimAbi.prepare runtime abiCache
  let foreignSymbols := profileit "preparation.providers.foreign_symbols" profile fun _ =>
    CompilerForeignSymbolTables.prepare lifecycle.calls.symbols
  let covarianceIndex := profileit "preparation.providers.covariance_index" profile fun _ =>
    CompilerQueryIndices.covariance program.input.covarianceQueries
  let signatureAbiIndex := profileit "preparation.providers.signature_abi_index" profile fun _ =>
    CompilerQueryIndices.signatureAbi runtime abiCache
  let arrays := profileit "preparation.providers.runtime_arrays" profile fun _ =>
    RuntimeArrayTypes.create owner |>.mapError reprStr
  let tls := profileit "preparation.providers.thread_local" profile fun _ => CompilerThreadLocal.ofProgram program
  let constants := profileit "preparation.providers.rebind_constants" profile fun _ => constants.withProgram program
  return {
    owner
    lifecycle
    functions := {functions with program}
    main := main.withProgram program
    intrinsics := intrinsics.withProgram program
    constants
    namedConstants := namedConstants.withProgram program
    namedGlobals := namedGlobals.withProgram program
    externStatics := externStatics.withProgram program
    pointers
    vtables
    namedAbi
    foreignSymbols
    covarianceIndex
    signatureAbiIndex
    initialArrays := arrays
    tls }

def prepare (input : LoweredProgram) : Except String Prepared :=
  prepareProfiled {} input

/-- The canonical predicate table belonging to all prepared vtable/cast facts. -/
def predicates (p : Prepared) : MIR.SharedTable PredicateListData := p.lifecycle.calls.symbols.facts.dynamicPredicates

private def lift (query : Except String A) : MachineHooks.M K User A :=
  match query with
  | .ok value => pure value | .error error => throw (.unsupported error)

/-- Resolve the exact compiler FnDef request at the current canonical source
terminator. Original request identity is distinct from the resolved method/shim
identity; trait methods may resolve to an implementation with a different DefId.
-/
def resolveCurrent (p : Prepared) (definition : MIR.DefId) (args : Array MIR.GenericArg) :
    MachineHooks.M K User CallInstance := do
  let frame ← MachineHooks.currentFrame
  let .mir location := frame.location | throw (.invalidProgram "callee resolution outside a MIR source location")
  let body ← lift do
    let some body := p.program.bundle.bodies[frame.bodyIdentity.index]? | throw "missing canonical source body"
    unless (← p.program.input.mirTables.bodyId frame.bodyIdentity.index) == frame.bodyId do
      throw "callee resolution canonical body ID mismatch"
    unless (← p.program.input.mirTables.body frame.bodyIdentity.index) == frame.body do
      throw "callee resolution canonical body metadata mismatch"
    let loaded ← CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls frame.functionInstance
    unless loaded.identity == frame.bodyIdentity do throw "callee resolution current full-instance/body mismatch"
    pure body
  let some id := body.body.basicBlocks[location.block]? | throw (.invalidProgram "callee resolution source block absent")
  let block ← lift (p.program.input.mirTables.mir.blocks.lookup id.index |>.mapError (fun id => s!"invalid callee-resolution block ID {id}"))
  unless location.statementIndex == block.statements.size do
    throw (.invalidProgram "callee resolution does not refer to a source terminator")
  lift do
    let resolution ← CallResolution.atSite p.lifecycle.calls.calls ⟨frame.bodyIdentity.index,location.block⟩
    let ty ← resolution.functionType
    match ← CompilerFunctionFacts.kind p.functions ty with
    | .FnDef expected expectedArgs =>
      unless definition == expected && args == expectedArgs do throw "original compiler FnDef request differs from current source call"
    | _ => throw "static instance resolution requested for an indirect compiler call"
    pure resolution.callee

/-- Concrete ExternAbi keeps source ABI/unwind identity separate from FnAbi's
canonical target convention. All full-callee hooks use the final shared tables.
The explicit base config retains physical memory/host/platform capabilities. -/
def executionHooks (p : Prepared) (image : AllocationImage.Imported)
    (vtableEngine : VTableMachine.Hooks K User Other) (userRelevantCrates : Array Nat)
    (base : ExecutionMachine.Config K User C Other ABI.ExternAbi Host) :
    ExecutionMachine.Config K User C Other ABI.ExternAbi Host :=
  let functions := CompilerFunctionPointers.hooks p.pointers image base.functions
  let vtableEngine := {vtableEngine with functions}
  let callCompiler := {base.calls.compiler with
    resolve := fun _ definition args => resolveCurrent p definition args
    functionSignature := fun _ layout => lift do
      let (count,abi) ← CompilerFunctionFacts.signature p.functions layout.ty
      pure (count,abi)
    functionKind := fun ty => lift (CompilerFunctionFacts.kind p.functions ty)
    fnAbiOfFnPtr := fun _ layout extra => lift (CompilerFunctionFacts.pointerAbi p.functions layout.ty extra)
    fnAbiOfInstance := fun _ callee extra =>
      match CompilerInstanceAbi.abiOfInstance p.lifecycle.instances callee extra with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error)}
  let dispatch := {base.calls.dispatch with loadMir := fun _ callee => CompilerCallPipeline.loadMir p.lifecycle.calls callee}
  let calls := {base.calls with compiler := callCompiler, dispatch}
  let helpers := {base.helpers with loadMir := fun _ callee => CompilerCallPipeline.loadMir p.lifecycle.calls callee}
  let facts := p.lifecycle.calls.symbols.facts.context
  CompilerExecutionFacts.hooks p.intrinsics {base with
    functions, calls, helpers
    rvalues := {base.rvalues with normalize := fun _ ty => lift (CompilerFacts.requiredType facts ty "normalized")}
    isRawPointer := fun _ ty => lift do
      let node ← p.runtime.node ty |>.mapError toString
      unless node.shapeStatus == .supported do throw "missing normalized pointer type shape"
      pure (node.shapeKind == .rawPointer)
    usizeLayout := fun _ => lift (p.primitiveLayout "usize")
    pointeeLayout := fun _ ty => lift do
      p.runtime.lookup (← CompilerFacts.requiredType facts ty "builtin_deref_explicit") |>.mapError toString
    lifecycle := CompilerLifecyclePipeline.lifecycleHooks p.lifecycle userRelevantCrates base.lifecycle
    virtual := CompilerVTableMachine.virtualLeaves p.vtables image vtableEngine base.virtual
    casts := {base.casts with
      vtableType := VTable.getPtrVTableType (CompilerVTableMachine.vtableHooks p.vtables image vtableEngine base.virtual.vtable)
      vtablePointer := VTable.getPointer (CompilerVTableMachine.vtableHooks p.vtables image vtableEngine base.virtual.vtable)
      vtableEntries := (CompilerVTableMachine.vtableHooks p.vtables image vtableEngine base.virtual.vtable).entries}
    validity := CompilerVTableMachine.validityHooks p.vtables image vtableEngine base.virtual.vtable base.validity}
end Miri.Input.CompilerProviders
