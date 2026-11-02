import duplicate_prefix.CurrentCallResourceSourceState
import duplicate_prefix.CurrentCallSourceHandoff
import duplicate_prefix.CurrentCallArguments

/-! Finite occurrence coverage for ONE actual scoped argument copy. The plain
copy keeps the input family; FnEntry validation installs the newly returned
child family. No statement quantifies over all program copies or histories. -/
namespace DuplicatePrefix.CurrentCallCopiedFamilies
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- Fixed family identities are attached to the actual argument, the plain
copied local, the validated child local, and the retained original destination.
The occurrences are explicit endpoint annotations, not inferred global coverage. -/
structure CopiedCallFamilies (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (data installed : Identities)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans)
    (initial copied doneFrame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) where
  input : Occurrence
  inputFamily : PointerInstance
  inputLoan : Loan
  inputLoanAt : data.interpretation.loans[call.sourceOwner]? = some inputLoan
  inputLoanFamily : inputLoan.pointer = input.slot
  retainedParentLoan : installed.interpretation.loans[call.sourceOwner + 1]? =
    some (CurrentCallOwnerRenaming.shiftLoan inputLoan)
  inputAt : data.interpretation.pointers[input.slot]? = some inputFamily
  inputAfter : installed.interpretation.pointers[input.slot]? = some inputFamily
  inputBits : inputFamily.value = input.bits
  inputArgument : argument = .pointer input.bits
  plainCopiedLocal : copied.locals[localId]?.map (·.value) = some (.live (.immediate
    (CurrentCallTypedSourceCopy.value options remaining span input.bits len).imm))
  child : Occurrence
  childFamily : PointerInstance
  childAt : installed.interpretation.pointers[child.slot]? = some childFamily
  childBits : childFamily.value = child.bits
  childSlot : child.slot = data.interpretation.pointers.size
  childOwnerLoan : installed.interpretation.loans[0]? =
    some ⟨child.slot,some (call.sourceOwner + 1),inputLoan.depth + 1⟩
  separateFamilies : input.slot ≠ child.slot
  validatedLocal : doneFrame.locals[localId]?.map (·.value) = some (.live (.immediate
    (CurrentCallTypedSourceCopy.value options remaining span child.bits len).imm))
  originalReturn : Occurrence
  returnFamily : PointerInstance
  returnLoan : Loan
  returnLoanAt : data.interpretation.loans[call.returnOwner]? = some returnLoan
  returnLoanFamily : returnLoan.pointer = originalReturn.slot
  returnAt : data.interpretation.pointers[originalReturn.slot]? = some returnFamily
  returnAfter : installed.interpretation.pointers[originalReturn.slot]? = some returnFamily
  returnBits : returnFamily.value = originalReturn.bits
  returnPointer : place.mplace.ptr = originalReturn.bits.withOptionalProvenance
  initialDestination : initial.returnPlace = CurrentCallArguments.destination place
  retainedDestination : doneFrame.returnPlace = initial.returnPlace
  oldOccurrences : installed.occurrences = data.occurrences
  oldOccurrenceLookups : ∀ (index : Nat) (pointer : PointerInstance), data.interpretation.pointers[index]? = some pointer →
    installed.interpretation.pointers[index]? = some pointer

/-- Consume only endpoint facts emitted by the SAME actual source-copy witness.
Initial family selection comes from owner/loan lookups, not equal pointer bits.
The actual scoped copy equation is retained with its finite family coverage. -/
theorem of_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : Before) (tracker : MachineHooks.BorrowState)
    (data : Identities) (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64)
    (place : MPlaceTy Provenance) (call : CallLoans)
    (D : CurrentDenotation before tracker argument len place call data)
    (W : UniformWindow before tracker data call.sourceOwner call.sourceId call.sourceOffset len.toNat .mut)
    (positive : 0 < len.toNat)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child (UInt64.ofNat call.sourceOffset) len)
    (frames : Array CompilerFrameContext.ActualFrame) (frame doneFrame : CompilerFrameContext.ActualFrame)
    (post : Before) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (originalDestination : frame.returnPlace = CurrentCallArguments.destination place)
    (retainedDestination : doneFrame.returnPlace = frame.returnPlace)
    (localValue : doneFrame.locals[localId]?.map (·.value) = some (.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (CurrentCallResourceFnEntry.child_pointer W output.tag child).value len ActualReferenceMetadata.reference).imm)))
    (actualCopy : MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before) = .ok () (Storage.withCurrent frames doneFrame post)) :
    let installed := CurrentCallSourceHandoff.install data call.sourceOwner W.loan
      (CurrentCallResourceFnEntry.child_pointer W output.tag child)
      (Window call.sourceId call.sourceOffset call.length)
    let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid W.pointer.value len
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before) = .ok () (Storage.withCurrent frames doneFrame post) ∧
    Nonempty (CopiedCallFamilies options remaining span data installed argument len place call frame copied doneFrame localId) := by
  dsimp only
  refine ⟨actualCopy,?_⟩
  have nonzero : len ≠ 0 := by intro zero; rw [zero] at positive; cases positive
  have sourceArgument : argument = .pointer W.pointer.value := by
    rcases D.sourceBinding with ⟨zero,_⟩ | ⟨_,pointer,arg,loan,family,loanAt,pointerAt,value,_,_⟩
    · exact False.elim (nonzero zero)
    · have sameLoan := Option.some.inj (loanAt.symm.trans W.loanAt)
      subst loan
      have sameFamily := Option.some.inj (pointerAt.symm.trans W.pointerAt)
      subst family
      rw [←value] at arg
      exact arg
  obtain ⟨_,returnPointer,returnPlace,returnLoan,returnFamily,returnLoanAt,returnAt,returnBits,_,_⟩ := D.returnBinding
  let installed := CurrentCallSourceHandoff.install data call.sourceOwner W.loan
    (CurrentCallResourceFnEntry.child_pointer W output.tag child) (Window call.sourceId call.sourceOffset call.length)
  refine ⟨{
    input := ⟨W.loan.pointer,W.pointer.value⟩
    inputFamily := W.pointer
    inputLoan := W.loan
    inputLoanAt := witness.parentLoanAt
    inputLoanFamily := rfl
    retainedParentLoan := CurrentCallSourceHandoff.parent_loan _ _ _ _ witness.parentLoanAt
    inputAt := witness.parentFamilyAt
    inputAfter := CurrentCallSourceHandoff.old_pointer _ _ _ _ witness.parentFamilyAt
    inputBits := rfl
    inputArgument := sourceArgument
    plainCopiedLocal := ?_
    child := ⟨data.interpretation.pointers.size,(CurrentCallResourceFnEntry.child_pointer W output.tag child).value⟩
    childFamily := CurrentCallResourceFnEntry.child_pointer W output.tag child
    childAt := witness.familyAt
    childBits := rfl
    childSlot := rfl
    childOwnerLoan := CurrentCallSourceHandoff.child_loan _ _ _ _ _
    separateFamilies := witness.distinctFamily
    validatedLocal := localValue
    originalReturn := ⟨returnLoan.pointer,returnFamily.value⟩
    returnFamily := returnFamily
    returnLoan := returnLoan
    returnLoanAt := returnLoanAt
    returnLoanFamily := rfl
    returnAt := returnAt
    returnAfter := CurrentCallSourceHandoff.old_pointer _ _ _ _ returnAt
    returnBits := rfl
    returnPointer := ?_
    initialDestination := originalDestination
    retainedDestination := retainedDestination
    oldOccurrences := rfl
    oldOccurrenceLookups := fun _ _ found => CurrentCallSourceHandoff.old_pointer _ _ _ _ found
  }⟩
  · simp [CurrentCallTypedSourceCopy.copiedFrame,valid]
  · rw [returnBits]
    exact returnPlace

end
end DuplicatePrefix.CurrentCallCopiedFamilies
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallCopiedFamilies" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved copied family dependency {dependency}"
