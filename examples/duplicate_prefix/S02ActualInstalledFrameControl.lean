import duplicate_prefix.S02SeparateDestinationInstalledFrame
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S02ActualInstalledFrameControl
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
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (entry : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine)) :
    entry.trackCallerArg = none ∧ entry.extra.userRelevance > 0 := by
  obtain ⟨reference,destId,destTag,frame,other,actual2,installedEq,_body,_identity,_callee,
    _location,_size,_slot1,_slot2,_metadata,_cache,_thread⟩ :=
    S02SeparateDestinationInstalledFrame.concrete_positive_installed id tag address len count input nonempty
      different returnTag returnConcrete
  have same : Storage.withCurrent #[] frame other = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have frameEq : frame = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  have control := RawRootInvocation.control before place input.contract.model.noDataRace
  have track : frame.trackCallerArg = root.frame.trackCallerArg := by
    rw [installedEq]
    exact PositiveRootInstalledFrame.track root _ count {} reference.id reference.tracker.global.nextPointerTag destId destTag
  have relevance : frame.extra.userRelevance = root.frame.extra.userRelevance := by
    rw [installedEq]
    exact PositiveRootInstalledFrame.relevance root _ count {} reference.id reference.tracker.global.nextPointerTag destId destTag
  rw [←frameEq]
  refine ⟨track.trans control.2.1,?_⟩
  rw [relevance,PositiveRootInstalledFrame.raw_relevance before place input.contract.model.noDataRace]
  decide

end
end DuplicatePrefix.S02ActualInstalledFrameControl

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ActualInstalledFrameControl.at_actual_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved installed frame control dependency {dependency}"
