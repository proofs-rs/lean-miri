import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

private def isError [DecidableEq ε] (actual : Except ε α) (expected : ε) : Bool :=
  match actual with
  | .ok _ => false
  | .error error => decide (error = expected)

private def mkId (value : UInt64) : IO AllocId :=
  match AllocId.ofUInt64 value with
  | some id => pure id
  | none => throw (IO.userError "test AllocId must be nonzero")

private def sourceAlloc : IO (Allocation CtfeProvenance Unit) := do
  match Allocation.fromBytes (Prov := CtfeProvenance) #[4, 5, 6] Align.ONE .Not with
  | .ok allocation => pure allocation
  | .error error => throw (IO.userError (toString error))

private def runtimeAlloc (mutability : Mutability := .Mut) :
    IO (Allocation Provenance Unit) := do
  match Allocation.fromBytes (Prov := Provenance) #[4, 5, 6] Align.ONE mutability with
  | .ok allocation => pure allocation
  | .error error => throw (IO.userError (toString error))

private def hooksFor (source : Allocation CtfeProvenance Unit)
    (runtime : Allocation Provenance Unit) (owned failBefore : Bool)
    (failAdjust failEval : Bool := false) :
    GlobalAllocationHooks Provenance Unit Unit (Array String) := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state definition =>
    let state := state.push s!"eval:{definition}"
    if failEval then ⟨memory, state, .error "initializer missing"⟩
    else ⟨memory, state, .ok source⟩
  beforeAccessGlobal := fun memory state id _ definition isWrite =>
    let defText := match definition with
      | none => "none"
      | some value => toString value
    let state := state.push s!"before:{id.value}:{defText}:{isWrite}"
    if failBefore then ⟨memory, state, .error "global access rejected"⟩
    else ⟨memory, state, .ok ()⟩
  adjustGlobalAllocation := fun memory state id _ =>
    let state := state.push s!"adjust:{id.value}"
    if failAdjust then ⟨memory, state, .error "adjust rejected"⟩
    else if owned then ⟨memory, state, .ok (.owned runtime)⟩
    else ⟨memory, state, .ok (.borrowed runtime)⟩
}

private def globalOutcomeTag (outcome : Except GlobalAccessError
    (AdjustedGlobalAllocation Provenance Unit)) : String :=
  match outcome with
  | .ok (.borrowed _) => "borrowed"
  | .ok (.owned _) => "owned"
  | .error (.notFound _) => "error:unknown"
  | .error (.dereferenceFunctionPointer _) => "error:function"
  | .error (.dereferenceVTablePointer _) => "error:vtable"
  | .error (.dereferenceTypeIdPointer _) => "error:typeid"
  | .error (.staticNotAStatic ..) => "error:not-static"
  | .error (.threadLocalStatic ..) => "error:thread-local"
  | .error (.unsupportedExternStatic ..) => "error:extern"
  | .error (.hookFailure hook _) =>
      if hook == "beforeAccessGlobal" then "error:before"
      else if hook == "adjustGlobalAllocation" then "error:adjust"
      else if hook == "evalStaticInitializer" then "error:initializer"
      else "error:other"
  | .error _ => "error:other"

private def printGlobalCase (label : String)
    (result : GlobalAllocationResult Provenance Unit Unit (Array String)) : IO Unit := do
  IO.println s!"global {label} outcome={globalOutcomeTag result.outcome} events={String.intercalate "," result.hooks.toList}"

private def globalMemory (id : AllocId) (kind : GlobalAllocationKind)
    (source : Allocation CtfeProvenance Unit) (mutability : Mutability)
    (payload : GlobalAllocationPayload) : MemoryState Provenance Unit Unit :=
  let base : MemoryState Provenance Unit Unit :=
    { (MemoryState.empty : MemoryState Provenance Unit Unit) with nextAllocId := 2 }
  MemoryState.setGlobalEntries (MemoryState.setIssuedIds base #[id])
    #[⟨id, kind, source.byteSize, source.align, mutability, some payload⟩]

private def contains (state : MemoryState Provenance Unit Unit) (id : AllocId) : Bool :=
  state.live.any fun entry => entry.1 == id

def main : IO Unit := do
  let id ← mkId 1
  let missingId ← mkId 2
  let source ← sourceAlloc
  let mutableRuntime ← runtimeAlloc .Mut
  let immutableRuntime ← runtimeAlloc .Not
  let memory := globalMemory id .memory source .Mut (.memory source)

  let sourceHooks := hooksFor source mutableRuntime false false
  let borrowed := MemoryLifecycle.getAllocRaw memory #[] id none sourceHooks
  check (isOk borrowed.outcome && !contains borrowed.memory id)
    "borrowed global adjustment must leave the local allocation map unchanged"
  check (borrowed.hooks == #["before:1:none:false", "adjust:1"])
    "global read must run access validation before adjustment"
  let .ok borrowedAllocation := borrowed.outcome
    | throw (IO.userError "borrowed global read failed")
  check (borrowedAllocation.byteSize == source.byteSize)
    "borrowed global conversion must return the adjusted allocation"

  let ownedHooks := hooksFor source mutableRuntime true false
  let owned := MemoryLifecycle.getAllocRaw memory #[] id (some ()) ownedHooks
  check (isOk owned.outcome && contains owned.memory id)
    "owned global adjustment must be cached locally"
  check (owned.memory.live[0]?.map (fun entry => entry.2.kind) == some (.machine ()))
    "owned global copies must use the machine global memory kind"

  let missingKind := MemoryLifecycle.getAllocRaw memory #[] id none ownedHooks
  check (isError missingKind.outcome (.missingGlobalMachineKind id) &&
      !contains missingKind.memory id && missingKind.hooks.size == 2)
    "missing GLOBAL_KIND must fail after hooks without inserting the allocation"

  let immutableHooks := hooksFor source immutableRuntime true false
  let immutableWrite := MemoryLifecycle.getAllocRawMut memory #[] id (some ()) immutableHooks
  check (isError immutableWrite.outcome (.readOnlyAllocation id) &&
      contains immutableWrite.memory id)
    "mutable global lookup must materialize before rejecting immutable memory"
  check (immutableWrite.hooks == #["before:1:none:true", "adjust:1"])
    "mutable global lookup must expose the write flag to access hooks"

  let cachedMutable := MemoryLifecycle.getAllocRawMut owned.memory owned.hooks id
      (some ()) ownedHooks
  check (isOk cachedMutable.outcome && cachedMutable.hooks == owned.hooks)
    "mutable access to an already local allocation must skip global hooks"

  let globalInfo ← match memory.getAllocInfo id with
    | .ok info => pure info
    | .error _ => throw (IO.userError "global allocation info was unavailable")
  check (globalInfo.kind == .liveData && globalInfo.mutability == .Mut &&
      globalInfo.size == source.byteSize && memory.isAllocLive id)
    "global metadata must report a live data allocation"
  let functionMemory := MemoryState.setGlobalEntries memory
    #[⟨id, .function, Size.ZERO, Align.ONE, .Not, some .function⟩]
  let functionInfo ← match functionMemory.getAllocInfo id with
    | .ok info => pure info
    | .error _ => throw (IO.userError "global function info was unavailable")
  check (functionInfo.kind == .function && functionInfo.size == Size.ZERO &&
      functionInfo.align == Align.ONE && functionMemory.isAllocLive id)
    "function globals must have source zero-sized function metadata"
  let functionAccess := MemoryLifecycle.getGlobalAlloc functionMemory #[] id false sourceHooks
  check (isError functionAccess.outcome (.dereferenceFunctionPointer id) &&
      functionAccess.hooks.isEmpty)
    "function allocations must not enter the memory adjustment path"

  let vaState := MemoryState.registerVaList (MemoryState.empty : MemoryState Provenance Unit Unit) id
  let vaInfo ← match vaState.getAllocInfo id with
    | .ok info => pure info
    | .error _ => throw (IO.userError "va-list info was unavailable")
  check (vaInfo.kind == .vaList && vaState.isAllocLive id)
    "va-list allocations must be live zero-sized records"
  let fnState := MemoryState.registerExtraFunction
      (MemoryState.empty : MemoryState Provenance Unit Unit) id
  check (fnState.isAllocLive id && (fnState.getAllocInfo id).toOption.map (·.kind) ==
      some .function)
    "machine-specific extra functions must participate in liveness and info"

  let deadState : MemoryState Provenance Unit Unit := {
    dead := #[⟨id, source.byteSize, source.align⟩]
  }
  let deadInfo ← match deadState.getAllocInfo id with
    | .ok info => pure info
    | .error _ => throw (IO.userError "dead allocation info was unavailable")
  check (deadInfo.kind == .dead && !deadState.isAllocLive id)
    "dead metadata must report layout without making an allocation live"
  check (deadState.getLiveAllocSizeAndAlign id .memoryAccess ==
      .error (.useAfterFree id .memoryAccess))
    "live-size lookup must retain the source use-after-free distinction"
  check (memory.getAllocInfo missingId == .error (.unavailable missingId))
    "unknown allocation info must be explicit rather than defaulted"

  let staticMemory := MemoryState.setGlobalEntries memory
    #[⟨id, .static, source.byteSize, source.align, .Not,
      some (.static 99 true false false)⟩]
  let staticHooks := hooksFor source mutableRuntime false false
  let staticRead := MemoryLifecycle.getGlobalAlloc staticMemory #[] id true staticHooks
  check (isOk staticRead.outcome && staticRead.hooks ==
      #["eval:99", "before:1:99:true", "adjust:1"])
    "static access must evaluate, validate, and adjust in source order"
  let threadLocalMemory := MemoryState.setGlobalEntries staticMemory
    #[⟨id, .static, source.byteSize, source.align, .Not,
      some (.static 99 true true false)⟩]
  let threadLocal := MemoryLifecycle.getGlobalAlloc threadLocalMemory #[] id false staticHooks
  check (isError threadLocal.outcome (.threadLocalStatic id 99) &&
      threadLocal.hooks.isEmpty)
    "thread-local statics must fail before initializer evaluation"
  let externMemory := MemoryState.setGlobalEntries staticMemory
    #[⟨id, .static, source.byteSize, source.align, .Not,
      some (.static 99 true false true)⟩]
  let externStatic := MemoryLifecycle.getGlobalAlloc externMemory #[] id false staticHooks
  check (isError externStatic.outcome (.unsupportedExternStatic id 99) &&
      externStatic.hooks.isEmpty)
    "Miri extern static access must remain explicitly unsupported"

  let failHooks := hooksFor source mutableRuntime true true
  let failAccess := MemoryLifecycle.getAllocRaw memory #[] id (some ()) failHooks
  check (isError failAccess.outcome
      (.globalAccess (.hookFailure "beforeAccessGlobal" "global access rejected")) &&
      failAccess.hooks == #["before:1:none:false"] && !contains failAccess.memory id)
    "global access hook failures must preserve hook state and stop conversion"

  let deadRaw := MemoryLifecycle.getAllocRaw deadState #[] id none sourceHooks
  check (isError deadRaw.outcome (.globalAccess (.notFound id)))
    "raw lookup must not turn dead metadata into a live allocation"

  -- These output rows are compared against the source-extracted
  -- get_global_alloc method, including both success ownership and hook order.
  printGlobalCase "memory-read"
    (MemoryLifecycle.getGlobalAlloc memory #[] id false sourceHooks)
  let diffBase : MemoryState Provenance Unit Unit :=
    { (MemoryState.empty : MemoryState Provenance Unit Unit) with nextAllocId := 3 }
  let diffIssued := MemoryState.setIssuedIds diffBase #[id, missingId]
  let differentialStatic := MemoryState.setGlobalEntries diffIssued
    #[⟨missingId, .static, source.byteSize, source.align, .Not,
      some (.static 22 true false false)⟩]
  printGlobalCase "static-write"
    (MemoryLifecycle.getGlobalAlloc differentialStatic #[] missingId true
      (hooksFor source mutableRuntime true false))
  printGlobalCase "function"
    (MemoryLifecycle.getGlobalAlloc functionMemory #[] id false sourceHooks)
  let vtableMemory := MemoryState.setGlobalEntries memory
    #[⟨id, .vtable, Size.ZERO, Align.EIGHT, .Not, some .vtable⟩]
  printGlobalCase "vtable"
    (MemoryLifecycle.getGlobalAlloc vtableMemory #[] id false sourceHooks)
  let typeIdMemory := MemoryState.setGlobalEntries memory
    #[⟨id, .typeId, Size.ZERO, Align.ONE, .Not, some .typeId⟩]
  printGlobalCase "typeid"
    (MemoryLifecycle.getGlobalAlloc typeIdMemory #[] id false sourceHooks)
  printGlobalCase "thread-local"
    (MemoryLifecycle.getGlobalAlloc threadLocalMemory #[] id false staticHooks)
  let nonStaticMemory := MemoryState.setGlobalEntries staticMemory
    #[⟨id, .static, source.byteSize, source.align, .Not,
      some (.static 11 false false false)⟩]
  printGlobalCase "not-static"
    (MemoryLifecycle.getGlobalAlloc nonStaticMemory #[] id false staticHooks)
  printGlobalCase "extern"
    (MemoryLifecycle.getGlobalAlloc externMemory #[] id false staticHooks)
  printGlobalCase "before-failure"
    (MemoryLifecycle.getGlobalAlloc memory #[] id false
      (hooksFor source mutableRuntime false true))
  printGlobalCase "adjust-failure"
    (MemoryLifecycle.getGlobalAlloc memory #[] id false
      (hooksFor source mutableRuntime false false true))
  let initFailureHooks := hooksFor source mutableRuntime false false false true
  printGlobalCase "initializer-failure"
    (MemoryLifecycle.getGlobalAlloc differentialStatic #[] missingId false initFailureHooks)
  let absent := (MemoryState.empty : MemoryState Provenance Unit Unit)
  printGlobalCase "unknown"
    (MemoryLifecycle.getGlobalAlloc absent #[] missingId false sourceHooks)
  IO.println "checks passed: global lookup, lazy caching, liveness, and info"
