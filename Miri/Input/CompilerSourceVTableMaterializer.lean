import Miri.Input.WorldVTableAllocationPlan
import Miri.Input.CompilerInitialVTableActions

/-! Scratch narrow factory binding for compiler-owned CTFE allocation images.
No runtime VTableMachine registry/global-root/native conversion is installed by
this module. Query memo ownership must be witnessed at an actual empty initial
TCX prefix; unknown preexisting memo families remain Unsupported. -/
namespace Miri.Input.CompilerSourceVTableMaterializer
open Miri.ABI Miri.Memory GenericSubstitution
open CompilerInitialAllocation WorldVTableAllocationPlan

structure MemoEntry where
  run : Nat
  key : QueryKey
  allocation : AllocId
structure Memo where
  ownedRuns : Array Nat := #[]
  entries : Array MemoEntry := #[]
structure State (P E K : Type) where
  allocator : AllocatorWorld P E K
  compiler : RuntimeArrayTypes.World
  memo : Memo := {}

private def sourceSymbols (compiler : RuntimeArrayTypes.World) : VTableActions.SymbolSource where
  validate := fun key => do
    match key with
    | .function key =>
      let .Item definition := key.kind | throw "source vtable function shim binding unavailable"
      unless (← compiler.arena.identity definition) == key.definition do
        throw "source vtable function physical identity mismatch"
      let some source := compiler.metadata.source.definitions[definition]?
        | throw "source vtable function declaration absent"
      let some header := source.callableSource | throw "source vtable function callable header absent"
      unless header.definitionKind == "associated_function" || header.definitionKind == "function" do
        throw "source vtable function source kind mismatch"
      let some template := source.genericTemplate | throw "source vtable function generic header absent"
      let arguments ← GenericInstantiationWorld.ofArguments compiler.arena 16384 key.arguments
      for argument in arguments do MirTemplate.validateClosed 16384 argument
      let _ ← template.instantiateSignature 16384 arguments
    | .vtable ty predicates =>
      let concrete ← GenericInstantiationWorld.ofType compiler.arena 16384 ty
      MirTemplate.validateClosed 16384 concrete
      for predicate in predicates do
        unless predicate.definitionPath.isNone && predicate.boundVariables.isEmpty && predicate.projectionTerm.isNone do
          throw "source symbolic vtable predicate binding is outside canonical ground slice"
        let identity ← compiler.arena.identity predicate.definitionId
        let declarations :=  compiler.metadata.normalizationContext.traits.traits.filter (·.definition == identity)
        let #[declaration] := declarations | throw "source symbolic vtable trait declaration absent or ambiguous"
        match predicate.kind with
        | .trait => unless !declaration.isAuto do throw "source symbolic principal is auto trait"
        | .autoTrait => unless declaration.isAuto do throw "source symbolic auto trait is not auto"
        | .projection => throw "source symbolic projection binding unavailable"
        let arguments ← GenericInstantiationWorld.ofArguments compiler.arena 16384 predicate.genericArgs
        unless declaration.parameters.size == arguments.size+1 do throw "source symbolic predicate generic arity mismatch"
        for argument in arguments do MirTemplate.validateClosed 16384 argument
    | _ => throw "source vtable factory symbolic key kind unavailable"
  materialize := fun key id => do
    match key with
    | .function _ => pure ⟨id,.function,.ZERO,.ONE,.Not,some .function⟩
    | .vtable .. => pure ⟨id,.vtable,.ZERO,compiler.metadata.target.defaultAddressSpacePointerSpec.pointerAlign,.Not,some .vtable⟩
    | _ => throw "source vtable factory symbolic metadata unavailable"

private def validateRun (run : Nat) (state : State P E K) : Except String Unit := do
  unless state.allocator.memory.activeInitialCompilerRun == some run do throw "source vtable factory run is not active"
  let some supply := state.allocator.memory.initialCompilerRuns.find? (·.token == run)
    | throw "source vtable factory source counter absent"
  if supply.exhausted || state.allocator.memory.idSupplyExhausted || state.allocator.memory.sourceAllocIdWorldActive then
    throw "source vtable factory source counter is fatal or conflicting"
  for row in state.allocator.typedDedup do
    if row.run == run then
      if let .vtable _ predicates := row.key then
        unless predicates.all (·.definitionPath.isNone) do
          throw "source vtable captured predicate-key canonicalization unavailable"

/-- An actual complete frontier1 has issued no source IDs, hence cannot already
contain any allocation-query Memory result. A larger unknown prefix is NOT a
miss certificate and never falls back to old compiler query answer rows. -/
def initializeFreshMemo (run : Nat) (state : State P E K) :
    Except String Unit × State P E K := Id.run do
  match validateRun run state with | .error error => return (.error error,state) | .ok _ => pure ()
  if state.memo.ownedRuns.contains run then return (.ok (),state)
  let some supply := state.allocator.memory.initialCompilerRuns.find? (·.token == run)
    | return (.error "source vtable query memo source run absent",state)
  unless supply.next == 1 &&
      !(state.allocator.memory.initialCompilerBindings.any (·.run == run)) &&
      !(state.allocator.typedDedup.any (·.run == run)) do
    return (.error "source vtable preexisting allocation-query memo is unknown",state)
  return (.ok (),{state with memo := {state.memo with ownedRuns := state.memo.ownedRuns.push run}})

private def failure (message : String) : CtfeQueryBridge.Failure String := .unsupported message
private def access (run : Nat) : Access (State P E K) String where
  compilerRun := run
  validateRun := fun run state => ((validateRun run state).mapError failure,state)
  lookupQuery := fun run key state =>
    if !state.memo.ownedRuns.contains run then
      (.error (failure "source vtable allocation-query memo capability absent"),state)
    else (.ok ((state.memo.entries.find? (fun row => row.run == run && decide (row.key = key))).map (·.allocation)),state)
  createUninit := fun size align state =>
    let allocation := Allocation.tryNew (Prov := CtfeProvenance) size align .Uninit
      (fun size _ => some (Array.replicate size.bytes.toNat 0))
    (allocation.mapError (fun error => failure s!"source vtable compiler bytes: {reprStr error}"),state)
  internFunction := fun run key salt state =>
    let (result,allocator) := VTableActions.internTyped state.compiler.metadata.target
      (sourceSymbols state.compiler) run (.function key) salt state.allocator
    (result.mapError failure,{state with allocator})
  materializeVptr := none
  reserveFreshMemory := fun run allocation state =>
    let (result,allocator) := VTableActions.reserveMemory state.compiler.metadata.target.base run allocation state.allocator
    (result.mapError failure,{state with allocator})
  publishQuery := fun run key id state =>
    if state.memo.entries.any (fun row => row.run == run && decide (row.key = key)) then
      (.error (failure "source vtable allocation-query publication duplicated key"),state)
    else (.ok (),{state with memo := {state.memo with entries := state.memo.entries.push ⟨run,key,id⟩}})
  internSymbolic := none -- Term-to-typed-predicate adapter deliberately not guessed.

/-- Real source bytes/provenance and central global reserve are bound here.
The source planner is rechecked, while memo hits skip all allocation effects.
No production interpreter hook selects this factory automatically. -/
def query (run work fuel : Nat) (noTraitVptr : Bool) (concrete : TypeId)
    (principal : Option TraitSelection.TraitRef) :
    CtfeQueryBridge.Action (State P E K) String AllocId := fun state =>
  let (initialized,state) := initializeFreshMemo run state
  match initialized with
  | .error error => (.error (failure error),state)
  | .ok () =>
    match (WorldVTableAllocationPlan.prepare work fuel noTraitVptr concrete principal).run state.compiler with
    | .error error => (.error (failure error),state)
    | .ok (plan,compiler) =>
      WorldVTableAllocationPlan.materialize (access run) plan {state with compiler}

/-- Symbolic program vtable identity is distinct from the allocation-query
Memory result. This typed entry point retains full predicates and salt. -/
def reserveSymbolic (run : Nat) (concrete : TypeId)
    (predicates : Array VtablePredicate) (salt : UInt64) :
    CtfeQueryBridge.Action (State P E K) String AllocId := fun state =>
  match validateRun run state with
  | .error error => (.error (failure error),state)
  | .ok () =>
    let (result,allocator) := VTableActions.internTyped state.compiler.metadata.target
      (sourceSymbols state.compiler) run (.vtable concrete predicates) salt state.allocator
    (result.mapError failure,{state with allocator})

/-- Adapter laws belong to the interpreter owner. The adapter imports the real
current memory through Store.withMemory and commits every successor, including
failure effects; it never selects a legacy registry or invents an allocation. -/
structure Binding (W P E K : Type) where
  getMemory : W → MemoryState P E K
  getStore : W → Store
  getCompiler : W → RuntimeArrayTypes.World
  getMemo : W → Memo
  commit : W → MemoryState P E K → Store → RuntimeArrayTypes.World → Memo → W

/-- Always imports live memory and derives central counter views. Both success
and failure commit the exact successor memory/store/compiler/memo state.
The interpreter owner must supply lawful getters/commit and install this hook. -/
def asAction (binding : Binding W P E K)
    (action : CtfeQueryBridge.Action (State P E K) String A) :
    CtfeQueryBridge.Action W String A := fun world =>
  let state : State P E K := {
    allocator := (binding.getStore world).withMemory (binding.getMemory world)
    compiler := binding.getCompiler world
    memo := binding.getMemo world }
  let (result,successor) := action state
  (result,binding.commit world successor.allocator.memory successor.allocator.store
    successor.compiler successor.memo)
end Miri.Input.CompilerSourceVTableMaterializer
