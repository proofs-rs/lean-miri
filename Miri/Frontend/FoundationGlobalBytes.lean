import Miri.Frontend.FoundationPhysicalRegistry
import Miri.Input.AllocationImage

/-! Global-byte preparation for a supplied finite memory graph. Source rules:
exporter/global_byte_queries.rs::discover and CompilerGlobalBytes.prepare select
immutable align-one allocations with no provenance and fully initialized bytes.
A nonempty candidate requires the source byte-interner key/salt identity state;
foundation currently does not retain it. No missing salt is interpreted as a
miss, and graph IDs never stand in for raw compiler or runtime AllocIds. -/
namespace Miri.Frontend.Foundation

/-- Identify eligible byte content only after validating its complete image and
initialization partition. This does not establish that a caller-supplied image
came from rustc, and does not resolve any byte-interner identity. -/
def globalByteCandidate (source : Input.AllocationMemory) : Except String (Option (Array UInt8)) := do
  let bytes ← source.bytesHex.checkedBytes
  unless bytes.size == source.sizeBytes do throw "global byte image size mismatch"
  let _ ← (Input.RuntimeMetadata.alignment source.alignBytes).mapError toString
  let mut cursor := 0
  let mut initialized := true
  for range in source.initializationRanges do
    unless range.startBytes == cursor && range.endBytesExclusive ≥ cursor &&
        range.endBytesExclusive ≤ source.sizeBytes do
      throw "global byte initialization ranges overlap, leave gaps or exceed storage"
    if range.endBytesExclusive > range.startBytes then
      initialized := initialized && range.initialized
    cursor := range.endBytesExclusive
  unless cursor == source.sizeBytes do throw "global byte initialization partition incomplete"
  if source.mutability != .immutable || source.alignBytes != 1 ||
      !source.relocations.isEmpty || !initialized then return none
  return some bytes

/-- Exact byte-query coverage when the supplied complete memory graph has no
eligible byte-interner keys. Eligible contents fail closed until foundation
retains source interner construction material. In particular, this cannot turn
a string literal into a fresh runtime allocation or invent 32 salt misses. -/
def globalBytesWithoutCandidates (initial : PhysicalTypeRegistry)
    (nodes : Array Input.AllocationNode) :
    Except String (PhysicalTypeRegistry × Input.Catalog.GlobalBytes) := do
  let (registry, strType) ← initial.intern (.primitive "str" "")
  for i in [:nodes.size] do
    let some node := nodes[i]? | throw "global byte graph row absent"
    unless node.id == i do throw "global byte graph identities must be dense"
    let some (.memory memory) := node.data | throw "foundation global byte graph requires memory material"
    unless node.kind == .memory && node.memory == some memory do
      throw "global byte graph memory payload disagrees"
    for relocation in memory.relocations do
      unless relocation.target < nodes.size do throw "global byte relocation target absent"
    if (← globalByteCandidate memory).isSome then
      throw "foundation byte-interner source key/salt identity material is missing"
  return (registry, { saltCount := 32, strType, coveredAllocations := nodes.map (·.id), candidates := #[] })

set_option autoImplicit false in
/-- Import explicit memory images through the fixed checked graph importer.
All allocation identity remapping, initialization and CTFE provenance conversion
remain in AllocationImage; this wrapper neither synthesizes source nodes nor
claims their compiler origin. Captured raw-ID worlds must still be installed
separately by CompilerAllocIdWorld before byte-key attachment. Non-memory nodes
remain unsupported. -/
def importMemoryGraph {P E K : Type} [DecidableEq K] (target : ABI.RuntimeTargetDataLayout)
    (nodes : Array Input.AllocationNode) (initial : Memory.MemoryState P E K) :
    Input.AllocationImage.ImportResult P E K := Id.run do
  for i in [:nodes.size] do
    let some node := nodes[i]? | return ⟨initial, .error "source memory graph row absent"⟩
    unless node.id == i && node.kind == .memory do
      return ⟨initial, .error "source memory graph requires dense memory identities"⟩
    let some (.memory memory) := node.data
      | return ⟨initial, .error "source memory graph payload absent"⟩
    unless node.memory == some memory do
      return ⟨initial, .error "source memory graph payload disagrees"⟩
  return Input.AllocationImage.importGraph target #[]
    ⟨fun _ => .error "static source material is unsupported"⟩ nodes initial

end Miri.Frontend.Foundation
