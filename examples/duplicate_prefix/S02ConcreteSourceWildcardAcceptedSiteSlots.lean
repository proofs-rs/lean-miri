import duplicate_prefix.S02ConcreteSourceWildcardSiteSlots

namespace DuplicatePrefix.S02ConcreteSourceWildcardAcceptedSiteSlots
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
noncomputable section

/-- The real installed positive-call frame supplies the remaining accepted-guard
locals independently of the return pointer's provenance. -/
theorem from_shape
    {before : Before} {place : MPlaceTy Provenance}
    (race : before.dataRace = none)
    (adjusted : Immediate Provenance)
    (count : UInt64) (sourceId : AllocId) (sourceTag : BorTag)
    (destinationId : AllocId) (destinationTag : BorTag)
    (entry site : CompilerFrameContext.ActualFrame)
    (installed : entry = PositiveRootInstalledFrame.installed
      (RawRootInvocation.root before place race) adjusted count {}
      sourceId sourceTag destinationId destinationTag)
    (shape : GenericFunctionEntryPrefix.Shape entry site count) :
    site.locals[15]? = some ⟨.dead,none⟩ ∧
    site.locals[16]? = some ⟨.dead,none⟩ := by
  let root := RawRootInvocation.root before place race
  have slots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place race) adjusted count {}
    sourceId sourceTag destinationId destinationTag
  have installed15 : entry.locals[15]? = some ⟨.dead,none⟩ := by
    rw [installed]
    simpa using slots ⟨15,by decide⟩
  have installed16 : entry.locals[16]? = some ⟨.dead,none⟩ := by
    rw [installed]
    simpa using slots ⟨16,by decide⟩
  exact ⟨(shape.keep 15 (by decide)).trans installed15,
    (shape.keep 16 (by decide)).trans installed16⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardAcceptedSiteSlots

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAcceptedSiteSlots.from_shape) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard accepted site-slots dependency {dependency}"
