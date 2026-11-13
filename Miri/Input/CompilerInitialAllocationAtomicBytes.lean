import Miri.Input.CompilerInitialAllocationWorld

/-! Source allocate_bytes_dedup against the authoritative COMPLETE typed store.
All u64 salts participate. A miss consumes the shared source/runtime reservation
boundary; the resulting global and key are committed together. No legacy byte
cache is consulted, and compatible non-key globals cannot cause reuse. -/
namespace Miri.Input.CompilerInitialAllocation.AtomicBytes
open Miri.Memory Miri.ABI
set_option autoImplicit false
variable {P E K : Type}
def reserve (target : TargetDataLayout) (run : Nat) (bytes : Array UInt8) (salt : UInt64)
    (world : AllocatorWorld P E K) : Except String AllocId × AllocatorWorld P E K := Id.run do
  if world.memory.sourceAllocIdWorldActive then
    return (.error "prepared and initial compiler source profiles conflict",world)
  unless world.memory.activeInitialCompilerRun == some run && world.runs.any (fun row => row.1 == run) do
    return (.error "complete initial compiler run is not the active source allocator",world)
  let some supply := world.memory.initialCompilerRuns.find? (fun row => row.token == run)
    | return (.error "active initial source supply is absent",world)
  if supply.exhausted || world.memory.idSupplyExhausted then
    return (.error "initial source allocation supply is fatal",world)
  let allocation : Allocation CtfeProvenance Unit ← match Allocation.fromBytesByteAlignedImmutable bytes with
    | .ok value => pure value
    | .error error => return (.error s!"allocate_bytes_dedup allocation: {error}",world)
  let key : MemoryKey := {
    bytes := bytes, initMask := allocation.initializationMask, alignment := 1, mutable := false,
    pointerBytes := (Size.fromBits target.pointerWidth.bits).bytes, littleEndian := target.endian == .little,
    provenance := allocation.provenanceMap }
  if let some id := lookupDedup world run (.memory key) salt then return (.ok id,world)
  let (memory,outcome) := world.memory.reserveAllocId
  let reserved := {world with memory}
  let id ← match outcome with
    | .ok id => pure id
    | .error error => return (.error s!"allocate_bytes_dedup reserve: {error}",reserved)
  let some raw := memory.initialCompilerSource? run id
    | return (.error "shared allocator failed to retain the consumed raw source identity",reserved)
  let global : GlobalAllocation := {
    allocId := id,kind := .memory,size := allocation.byteSize,align := .ONE,
    mutability := .Not,payload := some (.memory allocation) }
  let committed := {reserved with
    memory := memory.pushGlobal global,
    crosswalk := reserved.crosswalk.push (⟨run,raw⟩,id),
    symbolic := reserved.symbolic.push (id,.memory key),
    typedDedup := reserved.typedDedup.push ⟨run,.memory key,salt,id⟩}
  return (.ok id,committed)
end Miri.Input.CompilerInitialAllocation.AtomicBytes
