import duplicate_prefix.S02WildcardSourceWildcardSharedLenExact
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S02WildcardSourceWildcardInstalledReturnFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Runtime return-place and pop control fields of the exact installed wildcard call frame. -/
theorem facts
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (place : MPlaceTy Provenance) (race : before.dataRace = none)
    (address len count : UInt64)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (destId : AllocId) (destTag : BorTag)
    (entry : CompilerFrameContext.ActualFrame)
    (literal : entry = PositiveRootInstalledFrame.installed
      (RawRootInvocation.root before place race)
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      count {} reference.id reference.tracker.global.nextPointerTag destId destTag) :
    entry.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
    entry.returnContinuation = .stop true ∧ entry.vaList = #[] := by
  let root := RawRootInvocation.root before place race
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destId destTag
  refine ⟨?_,?_,?_⟩
  · rw [literal,metadata.2.2.2.2.1,(RawRootInvocation.control before place race).2.2.2]
    rfl
  · rw [literal,metadata.2.2.2.1]
    exact (RawRootInvocation.control before place race).2.2.1
  · rw [literal,metadata.2.2.2.2.2.1]
    rfl

end
end DuplicatePrefix.S02WildcardSourceWildcardInstalledReturnFacts

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardInstalledReturnFacts.facts) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard installed-return facts dependency {dependency}"
