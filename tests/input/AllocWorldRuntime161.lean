import Miri.Input.EvalPreparation
import Miri.Input.CompilerGlobalBytes
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.EvalMiriHostEffectsConstruction
import Miri.Input.InitialMachine
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.GlobalByteMachine
import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.VTableMachine

open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxHeartbeats 1000000

private structure RuntimeUser where
  functions : FunctionPointers.Registry Unit
  vtables : VTableMachine.Registry

private abbrev RuntimeState := MachineHooks.State MiriMemoryKind RuntimeUser

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def legacySourceNode (image : AllocationImage.Imported)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (id : AllocId) : Except String AllocationNode := do
  let some sourceId := memory.importedGraphIdForRuntime? id
    | throw "runtime global has no imported source identity"
  let some node := image.source.find? (·.id == sourceId)
    | throw "imported global source node is unavailable"
  pure node

private def legacyFunctionInstance (prepared : CompilerVTableRuntime.Prepared)
    (id : InstanceId) : Except String CallInstance := do
  let candidates := prepared.instances.filter (·.id == id)
  unless candidates.size == 1 do throw "missing or ambiguous complete compiler function instance"
  let some value := candidates[0]? | throw "compiler function instance missing"
  value.outcome

private def legacyGlobalFunction (prepared : CompilerVTableRuntime.Prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (id : AllocId) : Except String (Option CallInstance) := do
  let some node ← if memory.hasImportedRuntimeId id then
      some <$> legacySourceNode image memory id
    else
      let info ← (memory.getAllocInfo id).mapError (fun error => reprStr error)
      if info.kind == .function || info.kind == .vtable then
        throw "symbolic allocation has no imported compiler identity"
      pure none
    | return none
  let some (.function source) := node.data | return none
  let fnInstance ← legacyFunctionInstance prepared source.instanceId
  let tables := prepared.facts.context.program.compilerTables
  let definition ← lookupDefinitionId tables.definitions source.definitionId
  unless fnInstance.defId == definition do throw "global function/full-instance definition mismatch"
  let (args,next) ← lowerCompilerGenericArgs prepared.facts.context.loweringContext
    tables source.genericArgs
  unless next.definitions == tables.definitions && next.typeConstants == tables.typeConstants do
    throw "global function arguments require unprepared compiler identities"
  unless args == fnInstance.args do throw "global function/full-instance generic arguments mismatch"
  pure (some fnInstance)

private def legacyGlobalVTable (prepared : CompilerVTableRuntime.Prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (id : AllocId) : Except String (Option (Nat × Nat)) := do
  let some node ← if memory.hasImportedRuntimeId id then
      some <$> legacySourceNode image memory id
    else
      let info ← (memory.getAllocInfo id).mapError (fun error => reprStr error)
      if info.kind == .function || info.kind == .vtable then
        throw "symbolic allocation has no imported compiler identity"
      pure none
    | return none
  let some (.vtable source) := node.data | return none
  let _ ← prepared.facts.context.runtime.node source.typeId |>.mapError toString
  let predicates ← source.payload.getObjVal? "predicates"
  let token ← CompilerVTableFacts.exportedArrayToken prepared.facts predicates
  pure (some (source.typeId, token))

private def legacySeedFunctions (prepared : CompilerFunctionPointers.Prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (initial : FunctionPointers.Registry Unit) :
    Except String (FunctionPointers.Registry Unit) := do
  let mut registry := initial
  let input := prepared.calls.calls.program.input
  let some world := input.compilerAllocIdWorld | throw "fixture lacks prepared allocation world"
  unless memory.sourceAllocIdWorldActive do throw "prepared function catalog requires the active source AllocId world"
  unless image.source == input.allocations.filter (·.status == .supported) do
    throw "prepared function catalog allocation image differs from its owning program"
  validateCompilerAllocIdWorldRaw input.raw input.allocations (some world)
    |>.mapError fun error => s!"prepared AllocId world: {error}"
  for row in world.dedupCatalog do
    if row.keyKind == .function then
      let keyRuntime ← AllocationImage.runtimeId memory row.keyAllocationId
      let some keyCallee ← legacyGlobalFunction prepared.calls.symbols image memory keyRuntime
        | throw "prepared function key witness is not a symbolic function"
      for result in row.salts do
        if saltBound : result.salt < 32 then
          let resultRuntime ← AllocationImage.runtimeId memory result.allocationId
          unless memory.sourceAllocIdForRuntime? resultRuntime == some result.sourceAllocId do
            throw "prepared function result raw AllocId does not match the active memory world"
          let some resultCallee ← legacyGlobalFunction prepared.calls.symbols image memory resultRuntime
            | throw "prepared function salt result is not a symbolic function"
          unless resultCallee == keyCallee do
            throw "prepared function salt result does not match its exact compiler Instance key"
          let salt : Fin 32 := ⟨result.salt, saltBound⟩
          if let some old := registry.functions.find? (fun e => e.callee == keyCallee && e.salt == salt) then
            unless old.allocation == resultRuntime do throw "conflicting prepared function allocation for key/salt"
          else
            unless !(registry.functions.any (·.allocation == resultRuntime)) &&
                !(registry.extras.any (·.1 == resultRuntime)) do
              throw "prepared function allocation identity is already assigned"
            registry := {registry with functions := registry.functions.push ⟨keyCallee,salt,resultRuntime⟩}
        else throw "prepared function salt is outside the source key domain"
  pure registry

private def legacySeedVTables (prepared : CompilerVTableMachine.Prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (initial : VTableMachine.Registry) : Except String VTableMachine.Registry := do
  let mut registry := initial
  let input := prepared.calls.calls.program.input
  let some world := input.compilerAllocIdWorld | throw "fixture lacks prepared allocation world"
  unless memory.sourceAllocIdWorldActive do throw "prepared vtable catalog requires the active source AllocId world"
  unless image.source == input.allocations.filter (·.status == .supported) do
    throw "prepared vtable catalog allocation image differs from its owning program"
  validateCompilerAllocIdWorldRaw input.raw input.allocations (some world)
    |>.mapError fun error => s!"prepared AllocId world: {error}"
  for row in world.dedupCatalog do
    if row.keyKind == .vtable then
      let keyRuntime ← AllocationImage.runtimeId memory row.keyAllocationId
      let some key ← legacyGlobalVTable prepared.calls.symbols image memory keyRuntime
        | throw "prepared vtable key witness is not a symbolic vtable"
      for result in row.salts do
        if saltBound : result.salt < 32 then
          let resultRuntime ← AllocationImage.runtimeId memory result.allocationId
          unless memory.sourceAllocIdForRuntime? resultRuntime == some result.sourceAllocId do
            throw "prepared vtable result raw AllocId does not match the active memory world"
          let some resultKey ← legacyGlobalVTable prepared.calls.symbols image memory resultRuntime
            | throw "prepared vtable salt result is not a symbolic vtable"
          unless resultKey == key do
            throw "prepared vtable salt result does not match its exact type/predicate key"
          let salt : Fin 32 := ⟨result.salt, saltBound⟩
          if let some old := registry.entries.find? (fun e => e.typeId == key.1 &&
              e.dynamicType == key.2 && e.salt == salt) then
            unless old.allocation == resultRuntime do throw "conflicting prepared vtable allocation for key/salt"
          else
            unless !(registry.entries.any (·.allocation == resultRuntime)) do
              throw "prepared vtable allocation identity is already assigned"
            registry := {registry with entries := registry.entries.push ⟨key.1,key.2,salt,resultRuntime⟩}
        else throw "prepared vtable salt is outside the source key domain"
  pure registry

private def stateWith (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (user : RuntimeUser) : RuntimeState :=
  ⟨Stack.empty, {
    memory, borrowTracker := none, dataRace := none, threads := ThreadManager.initial false,
    raceAllocations := #[], allocationSpans := #[], user
  }⟩

private def functionHooks (salt : Fin 32) :
    FunctionPointers.Hooks MiriMemoryKind RuntimeUser Unit := {
  registry := RuntimeUser.functions
  putRegistry := fun user registry => {user with functions := registry}
  crossCrateInlineAlways := true
  inlineNever := fun _ => pure false
  chooseSalt := pure salt
  ptrGetAlloc := fun _ => pure none
  adjustRootPointer := fun id tag => pure (Pointer.new (Provenance.concrete id tag) Size.ZERO)
  importedFunction := fun _ => pure none
}

private def vtableHooks (prepared : EvalPreparation.Prepared)
    (functions : FunctionPointers.Hooks MiriMemoryKind RuntimeUser Unit) :
    VTableMachine.Hooks MiriMemoryKind RuntimeUser Unit := {
  functions
  registry := RuntimeUser.vtables
  putRegistry := fun user registry => {user with vtables := registry}
  target := prepared.compiler.runtime.target
  importedVTable := fun _ => pure none
}

private def runSelected (path : String) : IO Unit := do
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let attempt := EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  let memory := attempt.memory
  let some world := prepared.compiler.program.input.compilerAllocIdWorld |
    throw (IO.userError "selected archive omitted compiler_alloc_id_world")
  check memory.sourceAllocIdWorldActive "prepared source world is inactive"
  check (memory.sourceAllocIdNext == world.nextSourceAllocId) "prepared source frontier is not installed"
  check (world.rawPool.size == world.lastReservedSourceAllocId.toNat) "pool/frontier mismatch"
  check (world.nextSourceAllocId.toNat == world.lastReservedSourceAllocId.toNat + 1) "next source ID mismatch"
  for (row, index) in world.rawPool.toList.zipIdx do
    check (row.sourceAllocId.toNat == index + 1) s!"raw pool gap at index {index}"
  let some sentinel := world.rawPool[world.rawPool.size - 1]? |
    throw (IO.userError "final sentinel missing")
  check (sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone)
    "final source reservation is not the dangling sentinel"
  check (world.rawPool.any (·.status == .opaque)) "archived selected fixture has no opaque source reservations"
  let functionRows := world.dedupCatalog.filter (·.keyKind == .function)
  let vtableRows := world.dedupCatalog.filter (·.keyKind == .vtable)
  check (!functionRows.isEmpty && !vtableRows.isEmpty) "selected fixture lacks Fn/VTable rows"

  let image := prepared.image
  let functionRegistry ← must (CompilerFunctionPointers.seedImported prepared.compiler.pointers image memory
    (FunctionPointers.Registry.empty (Other := Unit)))
  let vtableRegistry ← must (CompilerVTableMachine.seedImported prepared.compiler.vtables image memory
    VTableMachine.Registry.empty)
  let legacyFunctionRegistry ← must (legacySeedFunctions prepared.compiler.pointers image memory
    (FunctionPointers.Registry.empty (Other := Unit)))
  let legacyVtableRegistry ← must (legacySeedVTables prepared.compiler.vtables image memory
    VTableMachine.Registry.empty)
  check (functionRegistry.functions.size == legacyFunctionRegistry.functions.size)
    "indexed function seed changed registry size from the legacy scan"
  for index in [:functionRegistry.functions.size] do
    let some indexed := functionRegistry.functions[index]? | throw (IO.userError "indexed function entry absent")
    let some legacy := legacyFunctionRegistry.functions[index]? | throw (IO.userError "legacy function entry absent")
    check (indexed.callee == legacy.callee && indexed.salt == legacy.salt &&
      indexed.allocation == legacy.allocation) s!"indexed function seed differs at position {index}"
  check (vtableRegistry.entries.size == legacyVtableRegistry.entries.size)
    "indexed vtable seed changed registry size from the legacy scan"
  for index in [:vtableRegistry.entries.size] do
    let some indexed := vtableRegistry.entries[index]? | throw (IO.userError "indexed vtable entry absent")
    let some legacy := legacyVtableRegistry.entries[index]? | throw (IO.userError "legacy vtable entry absent")
    check (indexed.typeId == legacy.typeId && indexed.dynamicType == legacy.dynamicType &&
      indexed.salt == legacy.salt && indexed.allocation == legacy.allocation)
      s!"indexed vtable seed differs at position {index}"

  let some functionRow := functionRows[0]? | throw (IO.userError "function conflict fixture missing")
  let some functionSalt := functionRow.salts[0]? | throw (IO.userError "function conflict salt missing")
  let functionRuntime ← must (AllocationImage.runtimeId memory functionSalt.allocationId)
  let functionKeyRuntime ← must (AllocationImage.runtimeId memory functionRow.keyAllocationId)
  let some functionKey ← must (legacyGlobalFunction prepared.compiler.lifecycle.calls.symbols image memory functionKeyRuntime)
    | throw (IO.userError "function conflict key has no exact instance")
  let some wrongAllocation := AllocId.ofUInt64 (UInt64.ofNat (2^64 - 1))
    | throw (IO.userError "function conflict AllocId is zero")
  if saltBound : functionSalt.salt < 32 then
    let duplicateKey : FunctionPointers.Registry Unit := {
      functions := #[⟨functionKey,⟨functionSalt.salt,saltBound⟩,wrongAllocation⟩,
        ⟨functionKey,⟨functionSalt.salt,saltBound⟩,functionRuntime⟩]
      extras := #[] }
    let indexedConflict := CompilerFunctionPointers.seedImported prepared.compiler.pointers image memory duplicateKey
    let legacyConflict := legacySeedFunctions prepared.compiler.pointers image memory duplicateKey
    match indexedConflict, legacyConflict with
    | .error indexed, .error legacy => do
        check (indexed == legacy) "indexed function conflict changed the legacy first-duplicate error"
    | _, _ => throw (IO.userError "indexed function seed lost first-duplicate conflict behavior")
  else throw (IO.userError "function conflict salt is outside source support")

  let some vtableRow := vtableRows[0]? | throw (IO.userError "vtable conflict fixture missing")
  let some vtableSalt := vtableRow.salts[0]? | throw (IO.userError "vtable conflict salt missing")
  let vtableRuntime ← must (AllocationImage.runtimeId memory vtableSalt.allocationId)
  let vtableKeyRuntime ← must (AllocationImage.runtimeId memory vtableRow.keyAllocationId)
  let some vtableKey ← must (legacyGlobalVTable prepared.compiler.lifecycle.calls.symbols image memory vtableKeyRuntime)
    | throw (IO.userError "vtable conflict key has no exact type/predicate")
  if saltBound : vtableSalt.salt < 32 then
    let duplicateKey : VTableMachine.Registry := {
      entries := #[⟨vtableKey.1,vtableKey.2,⟨vtableSalt.salt,saltBound⟩,wrongAllocation⟩,
        ⟨vtableKey.1,vtableKey.2,⟨vtableSalt.salt,saltBound⟩,vtableRuntime⟩] }
    let indexedConflict := CompilerVTableMachine.seedImported prepared.compiler.vtables image memory duplicateKey
    let legacyConflict := legacySeedVTables prepared.compiler.vtables image memory duplicateKey
    match indexedConflict, legacyConflict with
    | .error indexed, .error legacy => do
        check (indexed == legacy) "indexed vtable conflict changed the legacy first-duplicate error"
    | _, _ => throw (IO.userError "indexed vtable seed lost first-duplicate conflict behavior")
  else throw (IO.userError "vtable conflict salt is outside source support")

  let mismatchedImage := AllocationImage.Imported.ofSource #[] image.initializers
  let indexedPrefix := CompilerFunctionPointers.seedImported prepared.compiler.pointers mismatchedImage memory
    (FunctionPointers.Registry.empty (Other := Unit))
  let legacyPrefix := legacySeedFunctions prepared.compiler.pointers mismatchedImage memory
    (FunctionPointers.Registry.empty (Other := Unit))
  match indexedPrefix, legacyPrefix with
  | .error indexed, .error legacy => do
      check (indexed == legacy) "indexed function seed changed the legacy preflight error order"
  | _, _ => throw (IO.userError "indexed function seed did not preserve legacy image-identity preflight")
  check (functionRows.all (·.salts.size == 32)) "selected function row omitted salts"
  check (vtableRows.all (·.salts.size == 32)) "selected vtable row omitted salts"
  for row in functionRows do
    for result in row.salts do
      let runtimeId ← must (AllocationImage.runtimeId memory result.allocationId)
      check (memory.sourceAllocIdForRuntime? runtimeId == some result.sourceAllocId)
        s!"function salt {result.salt} lost its exact source witness"
      check (functionRegistry.functions.any (fun entry =>
        entry.salt.val == result.salt && entry.allocation == runtimeId))
        s!"function salt {result.salt} was not seeded"
  for row in vtableRows do
    for result in row.salts do
      let runtimeId ← must (AllocationImage.runtimeId memory result.allocationId)
      check (memory.sourceAllocIdForRuntime? runtimeId == some result.sourceAllocId)
        s!"vtable salt {result.salt} lost its exact source witness"
      check (vtableRegistry.entries.any (fun entry =>
        entry.salt.val == result.salt && entry.allocation == runtimeId))
        s!"vtable salt {result.salt} was not seeded"

  let user : RuntimeUser := {functions := functionRegistry, vtables := vtableRegistry}
  let initial := stateWith memory user
  let some functionEntry := functionRegistry.functions[0]? |
    throw (IO.userError "seeded function registry is empty")
  let fHooks := functionHooks functionEntry.salt
  let (afterFnHit, fnHit) := MachineHooks.run
    (FunctionPointers.functionPointer fHooks (.Instance functionEntry.callee)) initial
  match fnHit with
  | .error error => throw (IO.userError s!"selected function reserve hit failed: {reprStr error}")
  | .ok _ => pure ()
  check (afterFnHit.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "function hit consumed a fresh source AllocId"
  check (afterFnHit.machine.user.functions.functions.size == functionRegistry.functions.size)
    "function hit changed the seeded registry size"
  let missingFn : CallInstance := ⟨.Item 18446744073709551615, #[]⟩
  let (afterFnMiss, fnMiss) := MachineHooks.run
    (FunctionPointers.functionPointer fHooks (.Instance missingFn)) initial
  match fnMiss with
  | .error (.unsupported message) =>
    check (message.contains "not captured") "function miss returned an unrelated error"
  | .error error => throw (IO.userError s!"function miss returned unexpected error: {reprStr error}")
  | .ok _ => throw (IO.userError "uncaptured function key unexpectedly reserved")
  check (afterFnMiss.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "function miss consumed a fresh source AllocId"
  check (afterFnMiss.machine.user.functions.functions.size == functionRegistry.functions.size)
    "function miss mutated the function registry size"

  let some vtableEntry := vtableRegistry.entries[0]? |
    throw (IO.userError "seeded vtable registry is empty")
  let vtHooks := vtableHooks prepared fHooks
  let (afterVtHit, vtHit) := MachineHooks.run
    (VTableMachine.reserve vtHooks vtableEntry.typeId vtableEntry.dynamicType vtableEntry.salt) initial
  match vtHit with
  | .error error => throw (IO.userError s!"selected vtable reserve hit failed: {reprStr error}")
  | .ok id => check (id == vtableEntry.allocation) "vtable hit returned the wrong allocation"
  check (afterVtHit.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "vtable hit consumed a fresh source AllocId"
  let (afterVtMiss, vtMiss) := MachineHooks.run
    (VTableMachine.reserve vtHooks (vtableEntry.typeId + 18446744073709551615)
      vtableEntry.dynamicType vtableEntry.salt) initial
  match vtMiss with
  | .error (.unsupported message) =>
    check (message.contains "not captured") "vtable miss returned an unrelated error"
  | .error error => throw (IO.userError s!"vtable miss returned unexpected error: {reprStr error}")
  | .ok _ => throw (IO.userError "uncaptured vtable key unexpectedly reserved")
  check (afterVtMiss.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "vtable miss consumed a fresh source AllocId"

  let (afterFresh, freshResult) := MachineHooks.run
    (FunctionPointers.functionPointer fHooks (.Other ())) initial
  let freshPointer ← match freshResult with
    | .ok pointer => pure pointer
    | .error error => throw (IO.userError s!"fresh function reservation failed: {reprStr error}")
  let some freshId := freshPointer.provenance.getAllocId |
    throw (IO.userError "fresh function pointer lost its allocation identity")
  check (afterFresh.machine.memory.sourceAllocIdForRuntime? freshId == some world.nextSourceAllocId)
    "fresh reservation did not bind the next raw source identity"
  check (afterFresh.machine.memory.sourceAllocIdNext == world.nextSourceAllocId + 1)
    "fresh reservation did not advance the source frontier"
  check (afterFresh.machine.memory.hasFunctionPointer freshId)
    "fresh extra-function reservation was not retained as live state"

  let geometry ← must ((InitialMachine.geometry 64 "x86_64" false none).mapError reprStr)
  let machineConfig : InitialMachine.Configuration Unit Unit := {
    geometry, dummySpan := prepared.dummySpan, provenance := .default, addressMode := .managed,
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩,
    fixedScheduling := false, trackOutdatedLoads := false, weakMemory := true,
    backend := .vclocks, trackedTags := some #[], validation := .Shallow, alignment := .Int,
    affinity := none, muteOutput := true, hostUsizeBits := 64
  }
  let outer ← must ((InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
    (H := Unit) (D := Unit) (O := Unit) (Aff := Unit) (B := Unit) (Host := Unit)
    machineConfig afterFresh.machine.memory prepared.types
      {inputs := #[], cursor := 0} ()).mapError reprStr)
  let sourceState := Miri.Interpreter.ExecutionStateTransport.inward outer
  let some opaqueRow := world.rawPool.find? (·.status == .opaque) |
    throw (IO.userError "selected fixture has no opaque raw AllocId")
  let (afterOpaque, opaqueLookup) := MachineHooks.run
    (EvalMiriHostEffectsConstruction.sourceAllocIdFromImage image opaqueRow.sourceAllocId) sourceState
  match opaqueLookup with
  | .error (.unsupported message) =>
    check (message.contains "payload is opaque") "demanded opaque global returned the wrong error"
  | .error error => throw (IO.userError s!"demanded opaque global returned unexpected error: {reprStr error}")
  | .ok _ => throw (IO.userError "demanded opaque source global unexpectedly resolved")
  check (afterOpaque.machine.memory.sourceAllocIdWorldActive)
    "opaque lookup error lost the installed source AllocId world"
  let some serializedRow := world.rawPool.find? (·.status == .serialized) |
    throw (IO.userError "selected fixture has no serialized global")
  let some serializedGraphId := serializedRow.allocationId |
    throw (IO.userError "serialized raw row lacks its graph allocation")
  let serializedRuntimeId ← must (AllocationImage.runtimeId memory serializedGraphId)
  let (afterKnown, knownLookup) := MachineHooks.run
    (EvalMiriHostEffectsConstruction.sourceAllocIdFromImage image serializedRow.sourceAllocId) sourceState
  match knownLookup with
  | .ok (some id) => check (id == serializedRuntimeId) "serialized source AllocId returned the wrong runtime global"
  | .ok none => throw (IO.userError "serialized source AllocId unexpectedly returned none")
  | .error error => throw (IO.userError s!"serialized source AllocId lookup failed: {reprStr error}")
  check (afterKnown.machine.memory.sourceAllocIdWorldActive)
    "known source lookup lost the installed world"
  let (afterFreshLookup, freshNumberResult) := MachineHooks.run
    (EvalMiriHostEffectsConstruction.sourceAllocIdNumberFromImage image freshId) sourceState
  match freshNumberResult with
  | .ok number => check (number == world.nextSourceAllocId) "fresh live allocation returned the wrong raw source number"
  | .error error => throw (IO.userError s!"fresh source number lookup failed: {reprStr error}")
  let (afterFreshReverse, freshReverseResult) := MachineHooks.run
    (EvalMiriHostEffectsConstruction.sourceAllocIdFromImage image world.nextSourceAllocId) sourceState
  match freshReverseResult with
  | .ok (some id) => check (id == freshId) "fresh raw source number did not return its live runtime ID"
  | .ok none => throw (IO.userError "fresh raw source number unexpectedly returned none")
  | .error error => throw (IO.userError s!"fresh raw source lookup failed: {reprStr error}")
  check (afterFreshLookup.machine.memory.sourceAllocIdNext == afterFresh.machine.memory.sourceAllocIdNext &&
      afterFreshReverse.machine.memory.sourceAllocIdNext == afterFresh.machine.memory.sourceAllocIdNext)
    "source identity lookups mutated the fresh allocation frontier"

  let (byteState, byteAttach) := MachineHooks.run
    (CompilerGlobalBytes.attach prepared.compiler.program prepared.compiler.runtime) initial
  match byteAttach with
  | .error error => throw (IO.userError s!"byte-key attachment failed: {reprStr error}")
  | .ok _ => pure ()
  check byteState.machine.memory.byteGlobalKeysReady "byte key catalog was not attached"
  check byteState.machine.memory.sourceByteImageFamilyComplete
    "prepared byte family is not marked complete"
  let some (knownBytes, knownSalt, knownId) := byteState.machine.memory.byteGlobalKeys[0]? |
    throw (IO.userError "selected archive has no captured byte key")
  let (afterByteHit, byteHit) := MachineHooks.run
    (GlobalByteMachine.reserve knownBytes knownSalt) byteState
  match byteHit with
  | .error error => throw (IO.userError s!"captured byte reserve hit failed: {reprStr error}")
  | .ok id => check (id == knownId) "captured byte key returned the wrong allocation"
  check (afterByteHit.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "captured byte-key hit consumed a fresh source AllocId"
  let unknownBytes : Array UInt8 := #[255, 0, 161, 29]
  check (!byteState.machine.memory.byteGlobalKeys.any (·.1 == unknownBytes))
    "unknown byte probe unexpectedly matches the captured catalog"
  let (afterByteMiss, byteMiss) := MachineHooks.run
    (GlobalByteMachine.reserve unknownBytes knownSalt) byteState
  let unknownId ← match byteMiss with
    | .ok id => pure id
    | .error error => throw (IO.userError s!"complete-family byte miss failed: {reprStr error}")
  check (afterByteMiss.machine.memory.sourceAllocIdForRuntime? unknownId == some world.nextSourceAllocId)
    "complete-family byte miss did not reserve the next raw source ID"
  check (afterByteMiss.machine.memory.sourceAllocIdNext == world.nextSourceAllocId + 1)
    "complete-family byte miss did not advance the frontier"

  let exhaustedMemory := {memory with sourceAllocIdNext := 0}
  let exhaustedState := stateWith exhaustedMemory user
  let (failedState, afterExhausted) := MachineHooks.run
    (FunctionPointers.functionPointer fHooks (.Other ())) exhaustedState
  match afterExhausted with
  | .error (.resourceExhaustion _) => pure ()
  | .error _ => throw (IO.userError "fresh reservation returned an unexpected machine error")
  | .ok _ => throw (IO.userError "zero source AllocId unexpectedly reserved")
  -- MachineHooks.run retains the exhausted supply marker on failure.
  check failedState.machine.memory.sourceAllocIdExhausted
    "failed fresh reservation did not retain the source exhaustion state"
  IO.println s!"source157 live reservations PASS: opaque={world.rawPool.filter (·.status == .opaque) |>.size}, fn-hit/miss, vtable-hit/miss, byte-hit/miss, opaque-demand=Unsupported, fresh={world.nextSourceAllocId}, exhausted-state=retained"

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: AllocWorldRuntime161 <selected raw export.json>")
  runSelected path
