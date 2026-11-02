import duplicate_prefix.S02SeparateDestinationZeroCore
import duplicate_prefix.S02SeparateDestinationInstalledFrame
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02SeparateDestinationPacketSourceIdentity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The installed two-protector frame ties ZeroCore's source identity to the actual concrete argument. -/
theorem source_same
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
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine))
    (packet : S02SeparateDestinationZeroCore.Packet frame machine place) :
    packet.sourceId = reference.id ∧
    packet.sourceTag = reference.tracker.global.nextPointerTag := by
  obtain ⟨reference2,destId,destTag,installed,post,actual2,frameEq,_body,_identity,_callee,
    _location,_size,_slot1,_slot2,_metadata,_notConstructed,_thread⟩ :=
    S02SeparateDestinationInstalledFrame.concrete_positive_installed id tag address len count input nonempty
      different returnTag returnConcrete
  have same : Storage.withCurrent #[] installed post = Storage.withCurrent #[] frame machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have installedEq : installed = frame :=
    S02SeparateDestinationStateJoin.same_frame installed frame post machine same
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference2.id reference2.tracker.global.nextPointerTag)
      (Size.ofBytes (reference2.base+reference2.offset))) len ActualReferenceMetadata.reference).imm
  have h := PositiveRootInstalledFrame.two_protectors root adjusted count reference2.id destId
    reference2.tracker.global.nextPointerTag destTag
  have tracked : frame.extra.borrowTracker = some
      ({protectedTags := #[(reference2.id,reference2.tracker.global.nextPointerTag),(destId,destTag)]} : FrameState) := by
    rw [←installedEq,frameEq]
    exact h
  have frames : packet.borrowFrame =
      ({protectedTags := #[(reference2.id,reference2.tracker.global.nextPointerTag),(destId,destTag)]} : FrameState) :=
    Option.some.inj (packet.frameTracked.symm.trans tracked)
  have tags := packet.owned
  rw [frames] at tags
  have sourcePair : (packet.sourceId,packet.sourceTag) =
      (reference2.id,reference2.tracker.global.nextPointerTag) := by
    have index := congrArg (fun values : Array (AllocId × BorTag) => values[0]?) tags
    simpa using index.symm
  have refIds : reference2.id = reference.id := by
    have left := reference2.binding
    have right := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at left right
    exact left.1.symm.trans right.1
  have refTracker : reference2.tracker = reference.tracker :=
    Option.some.inj (reference2.enabled.symm.trans reference.enabled)
  have tagEq : packet.sourceTag = reference2.tracker.global.nextPointerTag :=
    congrArg Prod.snd sourcePair
  exact ⟨(congrArg Prod.fst sourcePair).trans refIds,by rw [tagEq,refTracker]⟩

end
end DuplicatePrefix.S02SeparateDestinationPacketSourceIdentity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPacketSourceIdentity.source_same) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved packet source identity dependency {dependency}"
