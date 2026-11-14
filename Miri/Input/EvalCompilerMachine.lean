import Miri.Input.CompilerSourceVTableMachine
import Miri.Input.CompilerProviders
import Miri.Input.EvalCoreMachine

/-! Production compiler/physical composition for the single EvalWorld. Compiler
identities are prepared once, symbolic registries use World.functions/vtables,
and address/salt decisions consume the same source-event tape as physical core.
Sources: step.rs/call.rs query sites; memory.rs global function/vtable allocation;
traits.rs symbolic vtables; machine.rs root-pointer adjustment. -/
namespace Miri.Input.EvalCompilerMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
abbrev Stored := EvalCoreMachine.Stored

/-- The one actual function registry; no compiler shadow allocation map. -/
def functions
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (base : FunctionPointers.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) O) :
    FunctionPointers.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) O :=
  ExecutionChoiceBindings.functionHooks EvalCoreMachine.tape {base with
    ptrGetAlloc := fun pointer => PointerMachine.ptrGetAlloc pointers pointer 0
    registry := fun user => user.payload.payload.user.functions
    putRegistry := fun user value => {user with payload := {user.payload with payload :=
      {user.payload.payload with user := {user.payload.payload.user with functions := value}}}}
    -- Root tag allocation occurs in FunctionPointers.rootPointer first. Address
    -- choice is then sampled exactly at this operation, preserving that effect.
    adjustRootPointer := fun id tag => do
      let address ← ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape pointers id (some .other)
      pure (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address))}

/-- Actual initial-run source reserve binding. Missing Store is Unsupported;
there is no default allocator or fallback to prepared vtable answers. -/
private def sourceVTableReserve (concrete : MIR.TyId) (dynamic : PredicateList) (salt : Fin 32) :
    MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) AllocId := do
  let state ← get
  let stored := state.machine.user.payload.payload.user
  let some store := stored.initialCompilerStore
    | throw (.unsupported "source vtable initial compiler Store not installed")
  let some run := state.machine.memory.activeInitialCompilerRun
    | throw (.unsupported "source vtable reserve requires active source run")
  let rawPredicates : Except String (Array Miri.Input.VtablePredicate) := dynamic.mapM fun id => do
    let some predicate := stored.types.metadata.source.predicates[id]?
      | throw "source vtable runtime predicate ID absent"
    pure {predicate with definitionPath := none}
  let predicates ← match rawPredicates with
    | .ok values => pure values
    | .error error => throw (.unsupported error)
  let factory : CompilerSourceVTableMaterializer.State Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind := {
    allocator := store.withMemory state.machine.memory
    compiler := stored.types
    memo := stored.initialVTableQueries }
  let (result,next) := CompilerSourceVTableMaterializer.reserveSymbolic run concrete predicates salt.val.toUInt64 factory
  -- Store derives its counter views from the successor actual MemoryState.
  let stored := {stored with
    types := next.compiler
    initialCompilerStore := some next.allocator.store
    initialVTableQueries := next.memo}
  let innerPayload := {state.machine.user.payload.payload with user := stored}
  let payload := {state.machine.user.payload with payload := innerPayload}
  let user := {state.machine.user with payload}
  set {state with machine := {state.machine with memory := next.allocator.memory, user := user}}
  let id ← match result with
    | .ok id => pure id
    | .error (.unsupported reason) => throw (.unsupported reason)
    | .error (.internal reason) => throw (.invalidProgram reason)
    | .error (.reported reason _) => throw (.callback reason)
    | .error (.tooGeneric _) => throw (.unsupported "source vtable input too generic")
  let state ← get
  let stored := state.machine.user.payload.payload.user
  if let some old := stored.vtables.entries.find? (fun entry => entry.typeId == concrete &&
      entry.dynamicType == dynamic && entry.salt == salt) then
    unless old.allocation == id do throw (.invalidProgram "source vtable runtime registry identity conflict")
  else
    unless !(stored.vtables.entries.any (·.allocation == id)) do
      throw (.unsupported "source vtable raw predicate alias needs canonical registry adapter")
    let stored := {stored with vtables := {entries := stored.vtables.entries.push ⟨concrete,dynamic,salt,id⟩}}
    let user := {state.machine.user with payload := {state.machine.user.payload with payload :=
      {state.machine.user.payload.payload with user := stored}}}
    set {state with machine := {state.machine with user := user}}
  return id

/-- The one actual symbolic vtable registry. Imported identities are installed
by CompilerProviders from the same image/source allocation mapping. -/
def vtables (prepared : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (functionEngine : FunctionPointers.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) O) :
    VTableMachine.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) O where
  functions := functionEngine
  registry := fun user => user.payload.payload.user.vtables
  putRegistry := fun user value => {user with payload := {user.payload with payload :=
    {user.payload.payload with user := {user.payload.payload.user with vtables := value}}}}
  target := prepared.runtime.target
  initialReserve := some sourceVTableReserve
  importedVTable := fun id => do
    match CompilerVTableRuntime.globalVTable prepared.lifecycle.calls.symbols image (← get).machine.memory id with
    | .ok result => pure result
    | .error error => throw (.unsupported error)

/-- Compiler binding must precede physical closure: retag/projection/scalar
closures capture the same actual vtable/compiler dictionary at construction. -/
def config
    (prepared : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (userRelevantCrates : Array Nat)
    (limits : ExecutionMachine.Limits) (choice : C) (failureRate : UInt64)
    (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (sync : P → Miri.Concurrency.SyncObject.AccessKind →
      PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (weakError : Miri.Concurrency.StoreBufferAllocError → StepError)
    (deallocation : AllocationMachine.DeallocationHooks MiriMemoryKind (User Os R P H D O Aff B Host) P)

    (base : ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost) :
    ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost :=
  let functionEngine := functions pointers base.functions
  let source := CompilerProviders.executionHooks prepared EvalProjectionMachine.arrays image
    (vtables prepared image functionEngine) userRelevantCrates {base with functions := functionEngine}
  EvalCoreMachine.config prepared.lifecycle.calls.symbols.facts prepared.lifecycle.calls.runtime
    limits choice failureRate spans pointers sync weakError deallocation source

end Miri.Input.EvalCompilerMachine
