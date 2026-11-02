import duplicate_prefix.S02ConcreteSourceWildcardSharedLenFullPacket
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardSiteSlots
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Remaining rejected-guard locals at the real shared site, independent of
return provenance. Only actual installed-frame shape is used. -/
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
    site.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
      some RootCompilerFacts.usizeLayout⟩ ∧
    site.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ := by
  let root := RawRootInvocation.root before place race
  have slots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place race) adjusted count {}
    sourceId sourceTag destinationId destinationTag
  have installed0 : entry.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [installed]
    simpa using slots ⟨0,by decide⟩
  have installed13 : entry.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [installed]
    simpa using slots ⟨13,by decide⟩
  exact ⟨shape.slot0.trans installed0,(shape.keep 13 (by decide)).trans installed13,
    shape.slot7,shape.slot8,shape.slot9,shape.slot10⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardSiteSlots

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardSiteSlots.from_shape) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard rejected site-slots dependency {dependency}"
