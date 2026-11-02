import duplicate_prefix.S02SeparateDestinationActualRejectedLedgerFlags
import duplicate_prefix.S02SeparateDestinationPhysicalInstalled
import duplicate_prefix.S02SeparateDestinationRejectedPhysicalTransport
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02SeparateDestinationRejectedPhysicalJoin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Physical return-place metadata from the same installed call is still valid at the rejected MIR10 state. -/
theorem at_rejected_state
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
    (installed : CompilerFrameContext.ActualFrame)
    (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (finalTree : BorrowTree)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed machine))
    (memory : post.memory = RetagEntry.updatedMemory
      (RootZeroCompleteState.tick options remaining span machine).memory reference.id sourceEntry finalTree)
    (addresses : post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses) :
    Nonempty (S03FinalReturnInputBounds.Destination post place) := by
  obtain ⟨otherFrame,otherMachine,otherActual,⟨destination⟩⟩ :=
    S02SeparateDestinationPhysicalInstalled.enters id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherMachine = Storage.withCurrent #[] installed machine :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have machineEq : otherMachine = machine := congrArg (fun s : RootState => s.machine) same
  have sourceId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have destinationId : destination.id = input.contract.destination.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun p : Pointer (Option Provenance) => p.provenance) physical
    simp only [Pointer.withOptionalProvenance,destination.concrete,returnConcrete] at provenance
    exact (Provenance.concrete.inj (Option.some.inj provenance)).1
  have separate : reference.id ≠ destination.id := by
    rw [sourceId,destinationId]
    exact different
  rw [←machineEq] at memory addresses
  exact ⟨S02SeparateDestinationRejectedPhysicalTransport.after_body options remaining span destination
    reference.id sourceEntry finalTree separate memory addresses⟩

end
end DuplicatePrefix.S02SeparateDestinationRejectedPhysicalJoin

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationRejectedPhysicalJoin.at_rejected_state) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected physical join dependency {dependency}"
