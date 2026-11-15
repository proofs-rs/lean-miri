import Miri.Input.CompilerVirtualLeaves
import Miri.Input.SourceCallFacts
import Miri.Input.CompilerProviders
import Miri.Input.CompilerCallFacts
import Miri.Input.CompilerExecutionCallLeaves
import Miri.Interpreter.ExecutionCalls

/-! Actual compiler call construction; no complete operational CallHooks record
is accepted and discarded. Every query key uses the canonical compilation. -/
namespace Miri.Input.CompilerCallConstruction
open Lean Miri.ABI Miri.Memory Miri.Interpreter
private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

private def sourceQuery (access : SourceCompilerWorld.Access (MachineHooks.State K U))
    (operation : SourceCompilerWorld.World → Except String A) : MachineHooks.M K U A := do
  let some world := access.get (← get) | throw (.unsupported "call dispatch World unavailable")
  lift (operation world)

/-- Canonical full compiler dictionary, including target-feature policy. -/
def compiler (p : CompilerProviders.Prepared) (budget : Nat)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U)) :
    ExecutionCallLeaves.Compiler (MachineHooks.State K U) C ABI.ExternAbi :=
  CompilerExecutionCallLeaves.make p budget world

/-- Layout-only compatibility is independent of instance lookup and World
state. Host wrappers must not construct a full compiler dictionary merely to
project this leaf, especially when their machine payload is polymorphic. -/
def argumentCompat (p : CompilerProviders.Prepared) (budget : Nat) (_choice : C)
    (caller callee : ArgAbi MIR.TyId) : EStateM StepError S Bool :=
  LayoutCompat.checkArgumentCompat
    (CompilerFacts.compatibilityQueries p.lifecycle.calls.symbols.facts.context)
    budget caller callee

/-- Foreign emulation and real backend hooks are actual source interpreters;
MIR loading is the same exact LoadedBody provider used by helper/root calls. -/
def dispatch (p : CompilerProviders.Prepared)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U))
    (foreign : Option (MachineHooks.M K U (ForeignItems.Hooks Provenance
      (MachineHooks.State K U) (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)))
    (backend : CallDispatchMachine.Backend (MachineHooks.State K U)) (dynSymName : Other → String) :
    CallDispatchMachine.Hooks (MachineHooks.State K U) C Other where
  foreign := foreign
  returnToBlock := fun target state =>
    let (after,result) := ControlFlow.returnToBlock target state
    match result with | .ok value => .ok value after | .error error => .error error after
  backend := backend
  dynSymName := dynSymName
  foreignScope := fun action => action
  isForeignItem := fun callee => if p.runtime.source.sourceMaterial.isSome then
    sourceQuery world (SourceCallFacts.isForeignItem · callee)
    else lift (CompilerCallFacts.isForeignItem p.intrinsics callee)
  symbolName := fun callee => if p.runtime.source.sourceMaterial.isSome then
    sourceQuery world (SourceCallFacts.symbolName · callee)
    else lift (CompilerCallFacts.symbolName p.intrinsics callee)
  loadMir := fun _ callee => CompilerCallPipeline.loadMir world callee

def leaves (p : CompilerProviders.Prepared)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U)) (compatibilityBudget : Nat)
    (foreign : Option (MachineHooks.M K U (ForeignItems.Hooks Provenance
      (MachineHooks.State K U) (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)))
    (backend : CallDispatchMachine.Backend (MachineHooks.State K U)) (dynSymName : Other → String)
    (llvm : CallInstance → MachineHooks.M K U (IntrinsicArchitecture.DispatchHooks Provenance (MachineHooks.State K U) C (RuntimePlace Provenance))) :
    ExecutionCallLeaves.Hooks (MachineHooks.State K U) C Other ABI.ExternAbi :=
  ⟨compiler p compatibilityBudget world,dispatch p world foreign backend dynSymName,llvm⟩
/-- Shared canonical vtable queries plus the exact compiler virtual leaves;
receiver reads, projections and pointer construction are not caller callbacks. -/
def virtual (p : CompilerProviders.Prepared)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U))
    (vtable : VTableHooks Provenance (MachineHooks.State K U) C CallInstance (FnAbi MIR.TyId))
    (alignment : PointerPlaceMachine.AlignmentContext U) : ExecutionCallLeaves.Virtual K U C :=
  ⟨CompilerVirtualLeaves.make p.lifecycle.calls world,vtable,alignment⟩

/-- Source frame metadata, preamble/checks and after-pop unwind processing.
Storage is the actual shared machine allocation context; no raw-push or
post-initialization success callback is accepted. -/
def lifecycle (p : CompilerProviders.Prepared)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U)) (userRelevantCrates : Array Nat)
    (storage : MachineHooks.StorageHooks K U) (identity : ExecutionCallLeaves.IdentityAccess U)
    (unwind : Unwind.Hooks K U C Other) : CallMachine.Lifecycle K U C where
  compiler := CompilerFrameMetadata.liveHooks world userRelevantCrates
  storage := storage
  freshLocalsIdentity := fun machine =>
    let (supply,label) := (identity.get machine.user).allocate
    ({machine with user := identity.put machine.user supply},label)
  preambleSpan := CompilerLifecycle.livePreambleSpan p.lifecycle.lifecycle world
  requiredConstants := CompilerLifecycle.liveRequiredConstants p.lifecycle.lifecycle world
  afterPop := fun choice frame unwinding => Unwind.afterStackPop unwind choice frame.extra unwinding

/-- Exact existing shared ThreadStacks supply, without a second counter. -/
def threadIdentity : ExecutionCallLeaves.IdentityAccess (ThreadStacks.Storage U) :=
  ⟨(·.identitySupply),fun user supply => {user with identitySupply := supply}⟩

/-- Actual source helper metadata plus the genuine dummy-signature compiler
query. Stack/origin operations are built by ExecutionCalls.helpers. -/
def helpers (p : CompilerProviders.Prepared)
    (world : SourceCompilerWorld.Access (MachineHooks.State K U)) (dummySpan : MIR.SpanRef)
    (fnAbiOfSignature : C → FunctionCalls.SignatureRequest ABI.ExternAbi → MachineHooks.M K U (FnAbi MIR.TyId)) :
    Except String (ExecutionCallLeaves.Helpers (MachineHooks.State K U) C ABI.ExternAbi) := do
  let unit ← p.primitiveLayout "unit"
  return {
    loadMir := fun _ callee => CompilerCallPipeline.loadMir world callee
    unitLayout := unit
    fnAbiOfSignature := fnAbiOfSignature
    callerLocationType := lift p.callerLocationType
    dummySpan }
end Miri.Input.CompilerCallConstruction
