import Miri.Input.SourcePhysical
import Miri.Input.SourceCompilerVTables
import Miri.Memory.MemoryState

/-! Exact symbolic vtable identities from a complete initial allocation snapshot.
Existing raw numbers are imported through a crosswalk; misses consume the one
MemoryState raw frontier shared with stack/heap/function allocation. There is no
second compiler supply, probe, fabricated salt answer or process-global cache. -/
namespace Miri.Input.SourceCompilerAllocationIdentity
open Miri.Memory Miri.Interpreter
abbrev World := SourceCompilerWorld.World
abbrev Entry := SourceAllocationIdentity.CanonicalVTable
private def snapshot (world : World) : Except String SourceAllocationIdentity.Material := do
  let some source := world.canonical.sourceMaterial | throw "allocation identity typed source absent"
  let some identity := source.allocationIdentity | throw "allocation identity initial snapshot unavailable"
  return identity

private def prepare (world : World) : Except String World := do
  if world.initialVTableIdentities.isSome then return world
  let identity ← snapshot world
  let some source := world.canonical.sourceMaterial | throw "allocation identity source absent"
  let some physical := source.physical | throw "allocation identity source types absent"
  let mut world := world
  let mut entries : Array Entry := #[]
  for entry in identity.dedup do
    if let .vtable type dynamicType := entry.key then
      let concrete ← SourceTypes.instantiate physical #[] #[] type
      let (updated,type) ← SourcePhysical.intern world concrete
      world := updated
      let concrete ← SourceTypes.instantiate physical #[] #[] dynamicType
      let (updated,dynamicType) ← SourcePhysical.intern world concrete
      world := updated
      let some dynamicNode := world.canonical.types[dynamicType]? | throw "initial vtable dynamic type absent"
      let .dynamicTraitObject predicates _ .Erased := dynamicNode.shape
        | throw "initial vtable key is not an erased dynamic type"
      let _ ← SourceCompilerVTables.erasedPair world type predicates
      if let some previous := entries.find? (fun previous => previous.type == type &&
          previous.predicates == predicates && previous.salt == entry.salt) then
        unless previous.rawId == entry.rawId do throw "conflicting initial canonical vtable key identities"
      else entries := entries.push ⟨type,predicates,entry.salt,entry.rawId⟩
  return {world with initialVTableIdentities := some entries}

/-- Existing source globals acquire only a fresh dense handle. This operation
must not reserve another compiler number or advance the source frontier. -/
def importKnown {P E K : Type} (identity : SourceAllocationIdentity.Material)
    (raw : UInt64) (memory : MemoryState P E K) :
    MemoryState P E K × Except String AllocId := Id.run do
  if !memory.sourceAllocIdWorldActive then return (memory,.error "source allocation identity world inactive")
  if memory.runtimeForSourceAllocId? raw |>.isSome then
    return (memory,.error "source allocation identity already imported")
  if !(identity.globals.any (·.rawId == raw)) then
    return (memory,.error "known source allocation absent from complete snapshot")
  let (reserved,result) := {memory with sourceAllocIdWorldActive := false}.reserveAllocId
  let reserved := {reserved with sourceAllocIdWorldActive := true}
  match result with
  | .error error => return (reserved,.error s!"source allocation dense handle: {reprStr error}")
  | .ok id =>
    let reserved := {reserved with opaqueSourceGlobalIds := reserved.opaqueSourceGlobalIds.filter (· != raw)}
    let reserved := reserved.setSourceAllocIdCrosswalks
      (reserved.sourceAllocIdByRuntime.push (id,raw)) (reserved.runtimeBySourceAllocId.push (raw,id))
    return (reserved,.ok id)

structure Attempt (P E K : Type) where
  world : World
  memory : MemoryState P E K
  outcome : Except String AllocId

/-- Reserve a symbolic key. Failure keeps any actually consumed dense/raw ID in
its returned memory, matching the fixed allocator's partial-effect order. -/
def demand {P E K : Type} (world : World) (memory : MemoryState P E K)
    (type : Nat) (predicates : PredicateList) (salt : Fin 32)
    (align : ABI.Align) : Attempt P E K := Id.run do
  let world ← match prepare world with
    | .ok world => pure world
    | .error error => return ⟨world,memory,.error error⟩
  let identity ← match snapshot world with
    | .ok identity => pure identity
    | .error error => return ⟨world,memory,.error error⟩
  if !memory.sourceAllocIdWorldActive ||
      (memory.sourceAllocIdNext != 0 && memory.sourceAllocIdNext < identity.frontier) then
    return ⟨world,memory,.error "vtable reservation does not share the captured source frontier"⟩
  let salt := UInt64.ofNat salt.val
  let some initial := world.initialVTableIdentities
    | return ⟨world,memory,.error "initial vtable identity materialization absent"⟩
  let entries := initial ++ world.derivedVTableIdentities
  let known := entries.find? (fun entry => entry.type == type && entry.predicates == predicates && entry.salt == salt)
  let (world,memory,result) ← match known with
    | some entry =>
      if let some id := memory.runtimeForSourceAllocId? entry.rawId then
        match memory.getAllocInfo id with
        | .ok info =>
          if info.kind == .vtable then return ⟨world,memory,.ok id⟩
          else return ⟨world,memory,.error "source vtable raw identity has non-vtable runtime metadata"⟩
        | .error _ => return ⟨world,memory,.error "source vtable runtime metadata absent"⟩
      let (memory,result) := importKnown identity entry.rawId memory
      pure (world,memory,result)
    | none =>
      let raw := memory.sourceAllocIdNext
      let (memory,result) := memory.reserveAllocId
      match result with
      | .error error => pure (world,memory,.error s!"vtable source reservation: {reprStr error}")
      | .ok id =>
        unless memory.sourceAllocIdForRuntime? id == some raw do
          return ⟨world,memory,.error "vtable source reservation crosswalk mismatch"⟩
        let world := {world with derivedVTableIdentities := world.derivedVTableIdentities.push ⟨type,predicates,salt,raw⟩}
        pure (world,memory,.ok id)
  match result with
  | .error error => return ⟨world,memory,.error error⟩
  | .ok id =>
    let globals := memory.globalsForId id
    if !globals.isEmpty then
      let [global] := globals.toList
        | return ⟨world,memory,.error "duplicate runtime metadata for source vtable"⟩
      unless global.kind == .vtable && global.size == .ZERO && global.align == align && global.mutability == .Not do
        return ⟨world,memory,.error "source vtable runtime metadata conflicts with target"⟩
      return ⟨world,memory,.ok id⟩
    let memory := MemoryState.pushGlobal memory ⟨id,.vtable,.ZERO,align,.Not,some .vtable⟩
    return ⟨world,memory,.ok id⟩
end Miri.Input.SourceCompilerAllocationIdentity
