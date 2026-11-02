import duplicate_prefix.CurrentCallResourceLenInvoke
namespace DuplicatePrefix.CurrentCallResourceLenCaller
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open LenUncachedFrontend
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
private theorem written_other (frame : CompilerFrameContext.ActualFrame) (source dest : MIR.LocalId)
    (layout : LocalLayout) (valid : dest<frame.locals.size) (value : Immediate Provenance) (different : source≠dest) :
    (ActualLocalCopy.written frame dest layout valid value).locals[source]?=frame.locals[source]? := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Ne.symm different]
private theorem cached_slot (frame : CompilerFrameContext.ActualFrame) (valid : 11<frame.locals.size)
    (stored : frame.locals[11]?=some ⟨.live (.immediate .uninit),none⟩) :
    (cachedCaller frame valid).locals[11]?=some ⟨.live (.immediate .uninit),some RootCompilerFacts.usizeLayout⟩ := by
  have fetched:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans stored)
  simp only [cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set_self,fetched]
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count)
theorem facts (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count)
    (base : UInt64) (valid : 11<(CurrentCallResourceLenInvoke.sharedFrame out frame shape base).locals.size) :
    (cachedCaller (CurrentCallResourceLenInvoke.sharedFrame out frame shape base) valid).locals.size=25 ∧
    (cachedCaller (CurrentCallResourceLenInvoke.sharedFrame out frame shape base) valid).locals[11]?=
      some ⟨.live (.immediate .uninit),some RootCompilerFacts.usizeLayout⟩ ∧
    (cachedCaller (CurrentCallResourceLenInvoke.sharedFrame out frame shape base) valid).extra.dataRace=none := by
  have stored : (CurrentCallResourceLenInvoke.sharedFrame out frame shape base).locals[11]?=
      some ⟨.live (.immediate .uninit),none⟩ := by
    change (ActualLocalCopy.written frame (RootReferenceFacts.destination true) _ _ _).locals[11]?=_
    exact (written_other frame 11 (RootReferenceFacts.destination true) _ _ _ (by decide)).trans shape.slot11
  refine ⟨?_,cached_slot _ valid stored,?_⟩
  · simpa only [cachedCaller,CurrentCallResourceLenInvoke.sharedFrame,CurrentCallResourceSharedStage.afterFrame,
      CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using shape.size
  · change frame.extra.dataRace=none
    rw [shape.extra]
    exact (CurrentCallResourceEntryFacts.metadata out).2.2.2.2.2.2.1.trans root.noClocks
end
end DuplicatePrefix.CurrentCallResourceLenCaller
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenCaller" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len caller dependency {dependency}"
