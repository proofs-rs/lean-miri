import duplicate_prefix.S02SeparateDestinationInstalledFrame
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02SeparateDestinationInstalledReturnFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The actual installed positive call has the concrete Return place and stop continuation for any count. -/
theorem ready
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
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine)) :
    frame.body = RootBody.reflected.body.body ∧
    frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
    frame.returnContinuation = .stop true ∧ frame.vaList = #[] ∧
    frame.extra.dataRace = none := by
  obtain ⟨reference,destId,destTag,installed,post,actual2,installedShape,body,
    _identity,_callee,_location,_size,_slot1,_slot2,_metadata,_notConstructed,_thread⟩ :=
    S02SeparateDestinationInstalledFrame.concrete_positive_installed id tag address len count input
      nonempty different returnTag returnConcrete
  have same : Storage.withCurrent #[] installed post = Storage.withCurrent #[] frame machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have frameEq := S02SeparateDestinationStateJoin.same_frame installed frame post machine same
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  have metadata := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destId destTag
  have control := RawRootInvocation.control before place input.contract.model.noDataRace
  have noClocks := root.noClocks
  rw [←frameEq]
  refine ⟨body,?_,?_,?_,?_⟩
  · rw [installedShape,metadata.2.2.2.2.1,control.2.2.2]
    rfl
  · rw [installedShape]
    exact metadata.2.2.2.1.trans control.2.2.1
  · rw [installedShape,metadata.2.2.2.2.2.1]
    rfl
  · rw [installedShape]
    exact metadata.2.2.2.2.2.2.1.trans noClocks

end
end DuplicatePrefix.S02SeparateDestinationInstalledReturnFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationInstalledReturnFrame.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved installed return frame dependency {dependency}"
