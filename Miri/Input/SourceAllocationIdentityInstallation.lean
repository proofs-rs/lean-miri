import Miri.Input.Model
import Miri.Memory.MemoryState

/-! Attach the complete initial raw-number frontier before runtime allocation.
Already imported source images keep their dense handles and gain only the exact
observed raw crosswalk. Opaque initial globals do not acquire fake payloads. -/
namespace Miri.Input.SourceAllocationIdentityInstallation
open Miri.Memory

def install {P E K : Type} (source : Option SourceMaterial) (nodes : Array AllocationNode)
    (memory : MemoryState P E K) : Except String (MemoryState P E K) := do
  let some source := source | return memory
  let some identity := source.allocationIdentity | return memory
  unless !memory.sourceAllocIdWorldActive && memory.live.isEmpty && memory.dead.isEmpty &&
      memory.extraFnPtrIds.isEmpty && memory.vaListIds.isEmpty && memory.byteGlobalKeys.isEmpty &&
      !memory.byteGlobalKeysReady && memory.sourceAllocIdByRuntime.isEmpty &&
      memory.runtimeBySourceAllocId.isEmpty do
    throw "initial allocation snapshot must precede runtime allocation and other raw-world installation"
  let mut byRuntime : Array (AllocId × UInt64) := #[]
  let mut bySource : Array (UInt64 × AllocId) := #[]
  for (graph,runtime) in memory.importedGlobalIds do
    let some node := nodes.find? (·.id == graph) | throw "initial source image graph absent"
    let some raw := node.sourceAllocId | throw "initial source image raw identity absent"
    let some global := identity.globals.find? (·.rawId == raw) | throw "initial source image absent from complete allocation snapshot"
    let kind := match global.kind with
      | .memory => AllocationKind.memory | .static => .static | .function => .function
      | .vtable => .vtable | .typeId => .typeId
    unless node.kind == kind && !(bySource.any (·.1 == raw)) do
      throw "initial source image kind/raw identity conflict"
    byRuntime := byRuntime.push (runtime,raw)
    bySource := bySource.push (raw,runtime)
  let unmapped := identity.globals.filterMap fun global =>
    if bySource.any (·.1 == global.rawId) then none else some global.rawId
  let memory := {memory with
    sourceAllocIdWorldActive := true
    sourceInitialFunctionDedupEmpty := !(identity.dedup.any (fun entry => SourceAllocationIdentity.Key.kind entry.key == SourceAllocationIdentity.Kind.function))
    sourceAllocIdNext := identity.frontier
    sourceAllocIdExhausted := false
    opaqueSourceGlobalIds := unmapped}
  return memory.setSourceAllocIdCrosswalks byRuntime bySource
end Miri.Input.SourceAllocationIdentityInstallation
