import duplicate_prefix.S02SameDestinationInstalledLocals
import duplicate_prefix.S02SameDestinationMachineGeometry
import duplicate_prefix.S02SeparateDestinationRejectedPurePrefix

namespace DuplicatePrefix.S02SameDestinationAcceptedEntryPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- From the original consistent call contract, a positive count
passes the real call entry and the nonzero-count pure MIR prefix. The call
result from three independently proved packets is aligned by determinism. -/
theorem actual_nonzero_prefix
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (countPositive : (0 : UInt64) < count) :
    ∃ (entry result : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) ∧
      GenericFunctionEntryPrefix.Shape entry result count := by
  obtain ⟨reference,entry,machine,actual,size,location,slots,noClocks,immediate⟩ :=
    S02SameDestinationInstalledLocals.ready id tag address len count input nonempty sameAllocation
      returnTag returnConcrete
  obtain ⟨_reference2,_destId,_destTag,entry2,machine2,actual2,_,body,identity,callee,_location,_size,
    _slot1,_slot2,_metadata,_notConstructed,_thread⟩ :=
    S02SameDestinationInstalledFrame.concrete_positive_installed id tag address len count input nonempty
      sameAllocation returnTag returnConcrete
  obtain ⟨_reference3,tracker,entry3,post,actual3,tracked,defaultMode,ghost,shallow,unchecked,noGc,fixed,_race⟩ :=
    S02SameDestinationMachineGeometry.after_exact id tag address len count input nonempty sameAllocation
      returnTag returnConcrete
  have same2 : Storage.withCurrent #[] entry machine = Storage.withCurrent #[] entry2 machine2 :=
    (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
  have same3 : Storage.withCurrent #[] entry machine = Storage.withCurrent #[] entry3 post :=
    (EStateM.Result.ok.inj (actual.symm.trans actual3)).2
  have frame2 : entry = entry2 := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same2
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have machine3 : machine = post := congrArg (fun s : RootState => s.machine) same3
  have nonzero : count ≠ 0 := by
    intro zero
    rw [zero] at countPositive
    have h := UInt64.lt_iff_toNat_lt.mp countPositive
    simp at h
  have validationPositive : 0 < options.limits.validation := by
    have lower : work before len ≤ options.limits.validation := input.contract.resources.configuredFuel.2.2.2
    unfold work at lower
    omega
  let sourceValue := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  have executed := S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals
    options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
    input.contract.model.debugOff (options.limits.validation - 1)
    (Nat.sub_add_cancel validationPositive).symm entry machine count nonzero
    (by rw [frame2]; exact body) (by rw [frame2]; exact identity)
    (by rw [frame2]; exact callee) location size sourceValue slots noClocks immediate tracker
    (by rw [machine3]; exact tracked) defaultMode (by rw [machine3]; exact ghost)
    (by rw [machine3]; exact shallow) (by rw [machine3]; exact unchecked)
    (by rw [machine3]; exact noGc) (by rw [machine3]; exact fixed)
  obtain ⟨result,trace,shape⟩ := executed
  exact ⟨entry,result,machine,actual,trace,shape⟩

end
end DuplicatePrefix.S02SameDestinationAcceptedEntryPrefix

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedEntryPrefix.actual_nonzero_prefix) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected entry-prefix dependency {dependency}"
