import Miri.Input.SourceCompilerWorld
import Miri.Input.CompilerGlobals
import Miri.Input.SourceCompilerAllocationIdentity

/-! Demand existing compiler memory images from the evaluation-local typed
World. Only the requested reachable graph receives canonical handles. Import
uses the fixed AllocationImage checks and keeps runtime allocation effects in
its returned memory, including failures. No raw AllocId becomes a runtime ID. -/
namespace Miri.Input.SourceCompilerAllocations
open Miri.Memory
private def reachable (limit : Nat) (targets : Nat → Except String (Array Nat))
    (root : Nat) : Except String (Array Nat) := go limit #[] root
where
  go (fuel : Nat) (seen : Array Nat) (id : Nat) : Except String (Array Nat) := do
    if seen.contains id then return seen
    let .succ fuel := fuel | throw "allocation graph traversal exhausted"
    let mut result := seen.push id
    for target in (← targets id) do
      result ← go fuel result target
    return result

def demand (world : SourceCompilerWorld.World) (sourceId : Nat) :
    Except String (SourceCompilerWorld.World × AllocationId) := do
  let some source := world.canonical.sourceMaterial | throw "typed source material absent"
  let some material := source.allocations | throw "typed source memory graph unavailable"
  let some root := material.images[sourceId]? | throw "demanded source memory image absent"
  if let some known := world.canonical.allocations.find? (·.sourceAllocId == some root.rawId) then
    return (world,known.id)
  let ids ← reachable (material.images.size + 1) (fun id => do
    let some image := material.images[id]? | throw "source memory image absent"
    pure (match image.payload with | .memory memory => memory.relocations.map (·.target) | .static _ => #[])) sourceId
  let mut mapping : Array (Nat × Nat) := #[]
  let mut next := world.canonical.allocations.size
  for id in ids do
    let some image := material.images[id]? | throw "source memory graph index absent"
    let matching := world.canonical.allocations.filter (·.sourceAllocId == some image.rawId)
    if matching.isEmpty then
      mapping := mapping.push (id,next)
      next := next + 1
    else
      let [node] := matching.toList | throw "canonical raw allocation identity ambiguous"
      mapping := mapping.push (id,node.id)
  let mut nodes := world.canonical.allocations
  for id in ids do
    let some image := material.images[id]? | throw "source memory graph index absent"
    let some (_,canonicalId) := mapping.find? (·.1 == id) | throw "source memory canonical mapping absent"
    let .memory sourceMemory := image.payload | throw "source static initializer demand not connected"
    let relocations ← sourceMemory.relocations.mapM fun relocation => do
      let some (_,target) := mapping.find? (·.1 == relocation.target)
        | throw "source relocation canonical mapping absent"
      return {relocation with target}
    let memory := {sourceMemory with relocations}
    let node : AllocationNode := {
      id := canonicalId
      sourceAllocId := some image.rawId
      kind := .memory
      memory := some memory
      data := some (.memory memory) }
    if canonicalId ≥ nodes.size then
      unless canonicalId == nodes.size do throw "canonical allocation handles are not dense"
      nodes := nodes.push node
  let some (_,result) := mapping.find? (·.1 == sourceId) | throw "demanded allocation handle absent"
  return ({world with canonical := {world.canonical with allocations := nodes}},result)

set_option autoImplicit false in
/-- Install only not-yet-imported demanded nodes, using the same World graph and
actual memory crosswalk. Static/function/vtable capabilities are unsupported. -/
def importDemanded {P E K : Type} [DecidableEq K] (target : ABI.RuntimeTargetDataLayout)
    (world : SourceCompilerWorld.World) (root : AllocationId) (memory : MemoryState P E K) :
    Except String (AllocationImage.ImportResult P E K) := do
  let nodes := world.canonical.allocations
  let ids ← reachable (nodes.size + 1) (fun id => do
    let some node := nodes[id]? | throw "demanded canonical memory image absent"
    let some (.memory image) := node.data | throw "demanded non-memory source allocation unsupported"
    pure (image.relocations.map (·.target))) root
  let pending ← (ids.filter (fun id => (memory.runtimeIdForExport? id).isNone)).mapM fun id => do
    let some node := nodes[id]? | throw "demanded canonical memory image absent"
    pure node
  let reserveSource := world.canonical.sourceMaterial.bind (·.allocationIdentity) |>.map fun identity =>
    fun (memory : MemoryState P E K) (node : AllocationNode) =>
      match node.sourceAllocId with
      | none => (memory,.error "demanded source image has no raw allocation identity")
      | some raw => SourceCompilerAllocationIdentity.importKnown identity raw memory
  return AllocationImage.importGraph target world.canonical.definitions CompilerGlobals.queries pending memory reserveSource
end Miri.Input.SourceCompilerAllocations
