import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.RootZeroCompletePrefix

/-! The actual zero-count body prefix from the current positive entry output.
This ends before pop and the physical return copy. Empty source entry remains
a separate obligation; no live-source requirement is imposed on that case. -/
namespace DuplicatePrefix.CurrentCallZeroCountReturn
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallEntry
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem reaches_return {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {out : Output input #[]} (facts : Facts out 0) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (out.frame 0) (out.machine 0))
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (out.machine 0)))) ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace = (out.frame 0).returnPlace ∧ result.extra = (out.frame 0).extra ∧
      CopyHelperCleanup.AllImmediate result := by
  let initial := root before #[] place input.machine.settings.noDataRace
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    len ActualReferenceMetadata.reference).imm
  have raw : initial.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  have frameEq := facts.frame_installed
  change out.frame 0 = PositiveRootInstalledFrame.installed initial value 0 {} call.sourceId
    tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag at frameEq
  have size : (out.frame 0).locals.size = 25 := by
    rw [frameEq];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have cells (i : Fin 25) := PositiveRootInstalledFrame.slot initial raw value 0 {} call.sourceId
    tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag i
  simp only [←frameEq] at cells
  obtain ⟨body,identity,callee,_,_,_,clocks,_,location⟩ := PositiveRootInstalledFrame.metadata initial value 0 {}
    call.sourceId tracker.global.nextPointerTag out.physical.id out.source.base.raw.output.global.nextPointerTag
  rw [←frameEq] at body identity callee clocks location
  have immediate : CopyHelperCleanup.AllImmediate (out.frame 0) := by
    rw [frameEq];exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  have model := out.settings 0
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by
      unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  obtain ⟨result,trace,_,_,_,extra,returnPlace,_,_,_,_,returnLocation,returnValue,all⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.machine.settings)
      model.debugOff fuel fuelEq (out.frame 0) (out.machine 0)
      (body.trans initial.body) (identity.trans initial.identity) (callee.trans initial.callee) location size
      (by simpa using congrArg LocalState.value (cells ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨3,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨2,by decide⟩))
      (clocks.trans initial.noClocks) immediate current enabled mode model.ghostOff model.shallow
      model.unchecked model.noGc model.fixedScheduler
  exact ⟨result,trace,returnLocation,returnValue,returnPlace,extra,all⟩

end
end DuplicatePrefix.CurrentCallZeroCountReturn

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallZeroCountReturn." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current zero-count dependency {dependency}"
