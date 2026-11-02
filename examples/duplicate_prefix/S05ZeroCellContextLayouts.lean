import duplicate_prefix.S05PriorCellLayouts
import duplicate_prefix.ProjectionMetadataFacts
import duplicate_prefix.RetagReferencePlace

/-! Equality of active value representations in two distinct compiler catalogs.
These are immutable query results, not a metadata replacement step, a frame
return/pop, or an ordinary-caller acceptance rule. Local type IDs remain distinct. -/
namespace DuplicatePrefix.S05ZeroCellContextLayouts
open Miri Miri.Input Miri.ABI Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem mutable_reference_layout :
    PriorCellMetadata.sliceReferenceLayout.layout = RootCompilerFacts.sliceLayout.layout := by
  decide +kernel

theorem slice_layout :
    PriorCellMetadata.sliceLayout.layout = ProjectionMetadataFacts.sliceLayout.layout := by
  decide +kernel

theorem byte_layout :
    PriorCellMetadata.byteLayout.layout = CopyCompilerFacts.byteLayout.layout := by
  decide +kernel

theorem bool_layout :
    PriorCellMetadata.boolLayout.layout = RootCompilerFacts.boolLayout.layout := by
  decide +kernel

/-- The two typed views carry exactly the same scalar pointer and length.
This is an equality of representations, with no execution or type-ID rewrite. -/
theorem slice_value_bits (target : TargetDataLayout) (pointer : Pointer Provenance) (len : UInt64) :
    (RetagReferencePlace.sliceValue target pointer len PriorCellMetadata.sliceReferenceLayout).imm =
      (RetagReferencePlace.sliceValue target pointer len RootCompilerFacts.sliceLayout).imm := rfl

end DuplicatePrefix.S05ZeroCellContextLayouts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellContextLayouts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved finite-context layout dependency {dependency}"
