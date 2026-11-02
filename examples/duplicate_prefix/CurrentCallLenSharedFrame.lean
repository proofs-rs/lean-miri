import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.CopyHelperSteps

namespace DuplicatePrefix.CurrentCallLenSharedFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

def frame (parent : CompilerFrameContext.ActualFrame) (valid : 12 < parent.locals.size)
    (value : RvalueImmTy Provenance) :=
  CopyHelperSteps.advance (ActualLocalCopy.written parent 12 SharedReferenceMetadata.sharedLayout valid value.imm) ⟨2,11⟩

/-- Only the actual local write and statement advance are normalized here. -/
theorem shape {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    (out : CurrentCallEntry.Output input #[]) (count : UInt64) (facts : CurrentCallEntry.Facts out count)
    (parent : CompilerFrameContext.ActualFrame)
    (shapeBefore : GenericFunctionEntryPrefix.Shape (out.frame count) parent count)
    (valid : 12 < parent.locals.size) (value : RvalueImmTy Provenance) :
    let result := frame parent valid value
    result.body = RootBody.reflected.body.body ∧
    result.bodyIdentity = RootBody.reflected.body.identity ∧
    result.functionInstance = RootBody.reflected.functionInstance ∧
    result.locals.size = 25 ∧ result.location = .mir ⟨2,12⟩ ∧
    result.extra.dataRace = none ∧
    result.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    result.locals[12]? = some ⟨.live (.immediate value.imm),some SharedReferenceMetadata.sharedLayout⟩ ∧
    result.returnPlace = (out.frame count).returnPlace ∧ result.extra = (out.frame count).extra := by
  have installed := facts.frame_installed
  have metadata := PositiveRootInstalledFrame.metadata
    (CurrentCallEntry.root before #[] place input.machine.settings.noDataRace)
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
      len ActualReferenceMetadata.reference).imm count {} call.sourceId tracker.global.nextPointerTag
    out.physical.id out.source.base.raw.output.global.nextPointerTag
  rw [←installed] at metadata
  have body := shapeBefore.body.trans (metadata.1.trans (CurrentCallEntry.root before #[] place input.machine.settings.noDataRace).body)
  have identity := shapeBefore.identity.trans (metadata.2.1.trans (CurrentCallEntry.root before #[] place input.machine.settings.noDataRace).identity)
  have callee := shapeBefore.callee.trans (metadata.2.2.1.trans (CurrentCallEntry.root before #[] place input.machine.settings.noDataRace).callee)
  have clocks : parent.extra.dataRace = none := by
    rw [shapeBefore.extra,metadata.2.2.2.2.2.2.1]
    exact (CurrentCallEntry.root before #[] place input.machine.settings.noDataRace).noClocks
  dsimp only [frame,CopyHelperSteps.advance]
  refine ⟨body,identity,callee,?_,rfl,clocks,?_,?_,shapeBefore.returnPlace,shapeBefore.extra⟩
  · simpa only [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using shapeBefore.size
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using shapeBefore.slot11
  · simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

end
end DuplicatePrefix.CurrentCallLenSharedFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallLenSharedFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Len frame dependency {dependency}"
