import duplicate_prefix.S02ConcreteSourceWildcardInstalled
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S02ConcreteSourceWildcardInstalledFrameControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The actual installed root frame retains the raw root's no-track-caller
field and positive user relevance for the Default/as_mut caller path. -/
theorem at_actual_call
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (entry : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine)) :
    entry.trackCallerArg = none ∧ entry.extra.userRelevance > 0 := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual2,destId,_packet⟩ :=
    S02ConcreteSourceWildcardInstalled.enters id tag address len count input nonempty
      different returnWildcard
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let sourceFrame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {sourceFrame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let frame := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let other := after.machine
  have installedEq : frame = PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag destination.id
      destination.tracker.global.nextPointerTag := rfl
  have same : Storage.withCurrent #[] frame other = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have frameEq : frame = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have control := RawRootInvocation.control before place input.contract.model.noDataRace
  have track : frame.trackCallerArg = root.frame.trackCallerArg := by
    rw [installedEq]
    exact PositiveRootInstalledFrame.track root _ count {} reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have relevance : frame.extra.userRelevance = root.frame.extra.userRelevance := by
    rw [installedEq]
    exact PositiveRootInstalledFrame.relevance root _ count {} reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  rw [←frameEq]
  refine ⟨track.trans control.2.1,?_⟩
  rw [relevance,PositiveRootInstalledFrame.raw_relevance before place input.contract.model.noDataRace]
  decide

end
end DuplicatePrefix.S02ConcreteSourceWildcardInstalledFrameControl

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardInstalledFrameControl.at_actual_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard installed frame control dependency {dependency}"
