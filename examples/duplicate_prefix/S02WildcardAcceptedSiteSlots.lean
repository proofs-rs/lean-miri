import duplicate_prefix.S02WildcardRejectedSiteFrame

namespace DuplicatePrefix.S02WildcardAcceptedSiteSlots
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The executed wildcard pure prefix fixes every remaining local consumed by
the shared Ref, length helper, rejected guard and false store. -/
theorem from_shape
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits
      remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (destinationId : AllocId) (destinationTag : BorTag)
    (entry frame : CompilerFrameContext.ActualFrame)
    (installed : entry = PositiveRootInstalledFrame.installed
      (RawRootInvocation.root before place input.contract.model.noDataRace)
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      count {} reference.id reference.tracker.global.nextPointerTag destinationId destinationTag)
    (shape : GenericFunctionEntryPrefix.Shape entry frame count) :
    frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[15]? = some ⟨.dead,none⟩ ∧
    frame.locals[16]? = some ⟨.dead,none⟩ ∧
    frame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
      some RootCompilerFacts.usizeLayout⟩ ∧
    frame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ := by
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have slots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destinationId destinationTag
  have installed0 : entry.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [installed]
    simpa using slots ⟨0,by decide⟩
  have installed13 : entry.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [installed]
    simpa using slots ⟨13,by decide⟩
  have installed15 : entry.locals[15]? = some ⟨.dead,none⟩ := by
    rw [installed]; simpa using slots ⟨15,by decide⟩
  have installed16 : entry.locals[16]? = some ⟨.dead,none⟩ := by
    rw [installed]; simpa using slots ⟨16,by decide⟩
  exact ⟨shape.slot0.trans installed0,(shape.keep 13 (by decide)).trans installed13,
    (shape.keep 15 (by decide)).trans installed15,
    (shape.keep 16 (by decide)).trans installed16,shape.slot7,shape.slot8,shape.slot9,shape.slot10⟩

end
end DuplicatePrefix.S02WildcardAcceptedSiteSlots

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedSiteSlots.from_shape) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard rejected site-slot dependency {dependency}"
