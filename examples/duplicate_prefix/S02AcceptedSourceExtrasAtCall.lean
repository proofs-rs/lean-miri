import duplicate_prefix.S02SeparateDestinationBothPhysicalReadyInstalled
import duplicate_prefix.S02SeparateDestinationSharedExact

namespace DuplicatePrefix.S02AcceptedSourceExtrasAtCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual installed call retains the initially coherent source extras row. -/
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
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (installed : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed machine)) :
    machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == reference.id) = some (reference.id,⟨none,#[]⟩) := by
  obtain ⟨other,firstFresh,destination,secondFresh,updated,child,actual2,_extra,_tagged,
      _runtime,_positive,_activity,_parent,_node,_parentTagged,_present,_same,_edge,_leaf,
      _hidden,_hiddenFrame,_sourceChild,_sourceNode,_sourceRaw,_sourceTracker,_sourceEnabled,
      _sourceLive,_sourceTagged,_sourcePresent,_sourceSame,_sourceHidden,_sourceRuntime,
      _sourcePositive,_sourceActive,_sourceRoots,_sourceOrder,_sourceShort,_physical,
      _updatedRoots,_updatedOrder,_updatedShort⟩ :=
    S02SeparateDestinationBothPhysicalReadyInstalled.enters_ready id tag address len count input
      nonempty different returnTag returnConcrete
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    other.tracker firstFresh other.id other.entry tag other.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete other.id other.tracker.global.nextPointerTag)
      (Size.ofBytes (other.base+other.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      other.id other.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector other.id other.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed2 := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have same : Storage.withCurrent #[] installed2 after.machine = Storage.withCurrent #[] installed machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have machineEq : after.machine = machine := congrArg (fun s : RootState => s.machine) same
  have preserved : after.machine.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras = _
    exact (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
  rw [←machineEq,preserved]
  exact input.metadata.extras_at reference.id reference.entry reference.live input.contract.model.noDataRace

end
end DuplicatePrefix.S02AcceptedSourceExtrasAtCall

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedSourceExtrasAtCall.at_actual_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted source extras dependency {dependency}"
