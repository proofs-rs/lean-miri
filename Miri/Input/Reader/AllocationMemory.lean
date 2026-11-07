import Miri.Input.Reader.Catalog
import Miri.Input.DecoderValues

namespace Miri.Input.Reader
open Lean

/-- Read allocation storage through checked shared-node lookups. References remain
in the catalog: decoding never constructs an expanded JSON allocation image. -/
def Catalog.readAllocationMemory (catalog : Catalog) (input : Json) (path : String) :
    Except String AllocationMemory := do
  let text := fun input key path => do catalog.string (← catalog.field input key path) path
  let nat := fun input key path => do catalog.natural (← catalog.field input key path) path
  let boolean := fun input key path => do catalog.boolean (← catalog.field input key path) path
  let bytes ← text input "bytes_hex" path
  unless DecoderValues.validHex bytes do throw s!"{path}.bytes_hex: malformed hexadecimal bytes"
  let values ← catalog.array (← catalog.field input "initialization_ranges" path) path
  let ranges ← values.mapIdxM fun index value => do
    let path := s!"{path}.initialization_ranges[{index}]"
    let state ← text value "state" path
    let initialized ← match state with
      | "initialized" => pure true
      | "uninitialized" => pure false
      | _ => throw s!"{path}.state: unrecognized initialization state `{state}`"
    let first ← nat value "start_bytes" path
    let last ← nat value "end_bytes_exclusive" path
    if last < first then throw s!"{path}: initialization range has end before start"
    pure (⟨initialized, first, last⟩ : InitRange)
  let values ← catalog.array (← catalog.field input "relocations" path) path
  let relocations ← values.mapIdxM fun index value => do
    let path := s!"{path}.relocations[{index}]"
    let reference ← catalog.inspect (← catalog.field value "target" path) s!"{path}.target"
    let .obj fields := reference | throw s!"{path}.target: expected allocation reference object"
    unless fields.toList.length == 1 && fields.contains "allocation_id" do
      throw s!"{path}.target: expected allocation reference object"
    let target ← nat reference "allocation_id" s!"{path}.target"
    let leanAllocId ← match Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat (target + 1)) with
      | some id => pure id
      | none => throw s!"{path}.target: export allocation ID cannot be represented as a nonzero CTFE identity"
    let immutable ← boolean value "immutable" path
    let sharedRef ← boolean value "shared_ref" path
    let ctfeProvenance ← match Miri.Memory.CtfeProvenance.fromParts (leanAllocId, immutable, sharedRef) with
      | .ok provenance => pure provenance
      | .error _ => throw s!"{path}: invalid CTFE provenance flags or allocation-ID width"
    let encoded ← text value "target_offset_encoded_bytes" path
    unless DecoderValues.validHex encoded do throw s!"{path}.target_offset_encoded_bytes: malformed hexadecimal bytes"
    pure ({
      storageOffsetBytes := ← nat value "storage_offset_bytes" path
      target := target
      targetOffsetEncodedBytes := encoded
      immutable := immutable
      sharedRef := sharedRef
      ctfeProvenance := ctfeProvenance
    } : Relocation)
  let size ← nat input "size_bytes" path
  if bytes.length / 2 != size then throw s!"{path}.bytes_hex: byte buffer length does not equal size_bytes"
  let mut cursor := 0
  for chunk in ranges do
    if chunk.startBytes != cursor then throw s!"{path}.initialization_ranges: ranges overlap or leave a gap"
    if chunk.endBytesExclusive > size then throw s!"{path}.initialization_ranges: range exceeds allocation size"
    cursor := chunk.endBytesExclusive
  if cursor != size then throw s!"{path}.initialization_ranges: ranges do not cover the allocation"
  for relocation in relocations do
    if relocation.storageOffsetBytes + relocation.targetOffsetEncodedBytes.length / 2 > size then
      throw s!"{path}.relocations: relocation's encoded pointer bytes exceed allocation size"
  let alignBytes ← nat input "align_bytes" path
  if alignBytes == 0 then throw s!"{path}.align_bytes: allocation alignment must be nonzero"
  return {
    sizeBytes := size
    alignBytes := alignBytes
    mutability := match ← text input "mutability" path with
      | "mutable" => .mutable
      | "immutable" => .immutable
      | other => .unknown other
    bytesHex := bytes
    initializationRanges := ranges
    relocations := relocations
  }

end Miri.Input.Reader
