import Miri.Frontend.Foundation
import Miri.Input.CatalogDecoderRuntime
import Miri.Input.RuntimeMetadata

/-! Finite target material uses the same required-field decoder and pure runtime
validator as the fixed interpreter. No target-triple inference or host defaults
are used. This validates representation and arithmetic consistency, not compiler
correctness or Rust/interpreter correspondence. -/
namespace Miri.Frontend.Foundation

/-- Decode the compiler's complete finite target facts from a foundation document.
The duplicate summary fields must agree; legacy foundation documents without the
complete material fail instead of silently recovering parser defaults. -/
def evidenceOfTarget (target : Target) : Except String Input.TargetDataLayoutEvidence := do
  let material := target.runtimeDataLayout
  let evidence ← Input.JsonReader.run Input.CatalogDecoder.targetDataLayout material.compress
  unless evidence.llvmDataLayout == target.dataLayout &&
      evidence.pointerWidthBits == target.pointerSizeBits &&
      evidence.endian == target.endian do
    throw "foundation target summary disagrees with complete target material"
  -- The shared runtime bridge checks the default bound. Check every retained
  -- address-space bound too, since those fields are source evidence only.
  for space in evidence.addressSpaceInfo do
    let expected ← match space.spec.pointerSizeBytes with
      | 2 => pure (2 ^ 15)
      | 4 => pure (2 ^ 31)
      | 8 => pure (2 ^ 61)
      | _ => throw "unsupported address-space pointer width for object bound"
    unless space.objectSizeBoundBytes == some expected do
      throw "address-space object bound disagrees with pointer width"
  return evidence

/-- Decode a complete foundation document before extracting target evidence. -/
def targetEvidence (source : Lean.Json) : Except String Input.TargetDataLayoutEvidence := do
  evidenceOfTarget (← decode source).target

def runtimeTargetOfTarget (target : Target) : Except String ABI.RuntimeTargetDataLayout := do
  (Input.RuntimeMetadata.importTarget (← evidenceOfTarget target)).mapError toString

/-- Construct the fixed interpreter's target as a pure value. Unsupported pointer
widths, invalid alignments and inconsistent object bounds remain errors. -/
def runtimeTarget (source : Lean.Json) : Except String ABI.RuntimeTargetDataLayout := do
  let evidence ← targetEvidence source
  (Input.RuntimeMetadata.importTarget evidence).mapError toString

end Miri.Frontend.Foundation
