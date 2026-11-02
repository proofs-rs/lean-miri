import duplicate_prefix.S02SameDestinationInstalledFrame
import duplicate_prefix.GenericFunctionEntryPrefix

namespace DuplicatePrefix.S02SameDestinationInstalledLocals
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact installed frame produced by the call has the local shape needed
by the nonzero-count pure prefix. This is a structural extraction, with no
interpreter-success or safety hypothesis. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      frame.locals.size = 25 ∧ frame.location = .mir ⟨0,0⟩ ∧
      (∀ i : Fin 25, frame.locals[i.val]? = some (
        if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
        else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
        else if 1 = i.val then ⟨.live (.immediate
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
              (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
          some ActualReferenceMetadata.reference⟩ else ⟨.dead,none⟩)) ∧
      frame.extra.dataRace = none ∧ CopyHelperCleanup.AllImmediate frame := by
  obtain ⟨reference,destId,destTag,frame,machine,actual,frameEq,_body,_identity,_callee,location,size,_slot1,_slot2,
    _metadata,_notConstructed,_thread⟩ :=
    S02SameDestinationInstalledFrame.concrete_positive_installed id tag address len count input nonempty
      sameAllocation returnTag returnConcrete
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  have raw := RawRootInvocation.locals before place input.contract.model.noDataRace
  have slot (i : Fin 25) := PositiveRootInstalledFrame.slot_option root raw adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destId destTag i
  have shape := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destId destTag
  have immediate := PositiveRootInstalledFrame.immediate root raw adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destId destTag
  refine ⟨reference,frame,machine,actual,size,location,?_,?_,?_⟩
  · intro i
    rw [frameEq]
    simpa only [root,adjusted] using slot i
  · rw [frameEq]
    exact shape.2.2.2.2.2.2.1.trans root.noClocks
  · rw [frameEq]
    exact immediate

end
end DuplicatePrefix.S02SameDestinationInstalledLocals

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationInstalledLocals.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete installed locals dependency {dependency}"
