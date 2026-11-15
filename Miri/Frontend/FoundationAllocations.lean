import Miri.Frontend.FoundationGlobalBytes
import Miri.Frontend.FoundationSourceConst
import Miri.Input.Model.SourceAllocations

/-! Existing compiler memory images captured from MIR ConstValue, not CTFE query
answers. Source graph IDs, raw rustc IDs and runtime IDs are distinct. Decoding
keeps raw provenance witnesses; AllocationImage remaps graph references only
when importing a demanded graph. Missing images and non-memory globals reject. -/
namespace Miri.Frontend.Foundation
open Lean

private def nat (j : Json) (key : String) : Except String Nat := j.getObjValAs? Nat key
private def bool (j : Json) (key : String) : Except String Bool := j.getObjValAs? Bool key
private def rawId (j : Json) (key : String) : Except String Memory.AllocId := do
  let n ← nat j key
  unless 0 < n && n < 2^62 do throw "source allocation identity exceeds CTFE ID range"
  let some id := Memory.AllocId.ofUInt64 (UInt64.ofNat n) | throw "zero source allocation identity"
  return id

/-- Decode complete finite memory source material. The exporter emitted these
images by traversing existing GlobalAlloc::Memory nodes without evaluation or
salt probes. This decoder does not certify compiler/exporter correspondence. -/
def sourceAllocationMaterial (document : Document) : Except String Input.SourceAllocations.Material := do
  let rows ← document.source.getObjValAs? (Array Json) "source_allocations"
  let mut rawIds := #[]
  for row in rows do
    let raw ← rawId row "source_alloc_id"
    if rawIds.contains raw then throw "duplicate raw source allocation identity"
    rawIds := rawIds.push raw
  let mut images := #[]
  for i in [:rows.size] do
    let some row := rows[i]? | throw "source allocation row missing"
    unless (← nat row "allocation_id") == i do throw "source allocation graph IDs must be dense"
    let some raw := rawIds[i]? | throw "source allocation raw ID missing"
    if (← row.getObjValAs? String "kind") == "static" then
      let id ← nat row "definition"
      let some definition := document.definitions[id]? | throw "source static definition absent"
      unless (← nat definition "definition_id") == id &&
          (← definition.getObjValAs? String "kind").startsWith "Static {" do
        throw "source static declaration identity/kind mismatch"
      let type ← nat row "type"
      unless type < document.types.size do throw "source static type absent"
      let initializer ← row.getObjVal? "initializer"
      let initializer ← match ← initializer.getObjValAs? String "status" with
        | "mir" => do
          let body ← SourceConstParser.body document (← initializer.getObjVal? "body")
          unless body.locals[0]? == some type do throw "static initializer return type differs from declaration"
          pure (.ok body)
        | "unavailable" => pure (.error (← initializer.getObjValAs? String "reason"))
        | _ => throw "source static initializer capability unknown"
      let declaration : Input.SourceAllocations.Static := {
        definition := ⟨← nat definition "crate_index",← nat definition "index"⟩
        path := ← definition.getObjValAs? String "path"
        type
        mutable := ← bool row "mutable"
        nested := ← bool row "nested"
        threadLocal := ← bool row "thread_local"
        foreignItem := ← bool row "foreign_item"
        initializer }
      images := images.push ⟨i,raw.value,.static declaration⟩
      continue
    unless (← row.getObjValAs? String "kind") == "memory" do throw "non-memory/static source global unsupported"
    let mut relocations := #[]
    for relocation in (← row.getObjValAs? (Array Json) "relocations") do
      let target ← nat relocation "target"
      let some expectedRaw := rawIds[target]? | throw "source relocation graph target missing"
      let raw ← rawId relocation "target_source_alloc_id"
      unless raw == expectedRaw do throw "source relocation raw identity disagrees with target graph row"
      let immutable ← bool relocation "immutable"
      let sharedRef ← bool relocation "shared_ref"
      if immutable && !sharedRef then throw "immutable source provenance must also be shared"
      let provenance ← (Memory.CtfeProvenance.fromParts (raw, immutable, sharedRef)).mapError reprStr
      let bytes ← relocation.getObjValAs? String "target_offset_encoded_bytes"
      let _ ← Input.decodeAllocationHex bytes
      relocations := relocations.push ⟨← nat relocation "storage_offset_bytes", target,
        bytes, immutable, sharedRef, provenance⟩
    let initializationRanges ← (← row.getObjValAs? (Array Json) "initialization_ranges").mapM fun range => do
      return Input.InitRange.mk (← bool range "initialized") (← nat range "start_bytes")
        (← nat range "end_bytes_exclusive")
    let memory : Input.AllocationMemory := {
      sizeBytes := ← nat row "size_bytes", alignBytes := ← nat row "align_bytes",
      mutability := if ← bool row "mutable" then .mutable else .immutable,
      bytesHex := .image (← Input.decodeAllocationHex (← row.getObjValAs? String "bytes_hex")),
      initializationRanges, relocations }
    -- Check storage partition and size before exposing source rows. Relocation
    -- pointer width/storage and target mapping remain in the checked importer.
    let _ ← globalByteCandidate memory
    images := images.push ⟨i,raw.value,.memory memory⟩
  let material : Input.SourceAllocations.Material := ⟨images⟩
  Input.SourceAllocations.validate material
  return material

/-- The older memory-image adapter has an explicit memory-only domain. The
normal source path consumes the complete typed graph above. -/
def sourceMemoryGraph (document : Document) : Except String (Array Input.AllocationNode) := do
  (← sourceAllocationMaterial document).images.mapM fun image => do
    let .memory memory := image.payload | throw "memory-only image adapter received a non-memory global"
    return {
      id := image.id
      sourceAllocId := some image.rawId
      kind := .memory
      memory := some memory
      data := some (.memory memory) }

/-- Map an allocation-bearing constant to the existing fixed MIR representation
without converting graph identities into pointer addresses or runtime IDs. -/
def sourceAllocationConstant (document : Document) (source : Json) : Except String MIR.ConstValue := do
  let nodes ← sourceMemoryGraph document
  let allocation ← nat source "allocation"
  unless allocation < nodes.size do throw "constant source allocation absent"
  match ← source.getObjValAs? String "kind" with
  | "allocation_slice" => return .Slice allocation (← nat source "metadata")
  | "allocation_indirect" => return .Indirect allocation (← nat source "offset_bytes")
  | "allocation_pointer" =>
    let immutable ← bool source "immutable"
    let sharedRef ← bool source "shared_ref"
    if immutable && !sharedRef then throw "immutable constant provenance must also be shared"
    return .Scalar (.Ptr (.Allocation allocation (← nat source "offset_bytes") immutable sharedRef))
  | _ => throw "unsupported allocation constant source kind"

set_option autoImplicit false in
/-- Demand source images and import with the existing checked allocation graph
semantics. Byte-interner attachment remains a separate, explicitly unsupported
step for eligible byte contents without its source key/identity construction. -/
def importSourceMemory {P E K : Type} [DecidableEq K] (document : Document)
    (initial : Memory.MemoryState P E K) : Except String (Input.AllocationImage.ImportResult P E K) := do
  let target ← runtimeTargetOfTarget document.target
  return importMemoryGraph target (← sourceMemoryGraph document) initial

end Miri.Frontend.Foundation
