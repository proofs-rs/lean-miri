import duplicate_prefix.S02SeparateDestinationBothPhysicalReadyInstalled
import duplicate_prefix.S02SeparateDestinationEntryIdentity

namespace DuplicatePrefix.S02SeparateDestinationZeroExtras
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual post-init machine retains the initially empty synchronization
row for the distinct concrete return allocation. -/
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
      .concrete input.contract.destination.id returnTag) :
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      machine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == input.contract.destination.id) =
          some (input.contract.destination.id,⟨none,#[]⟩) := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,child,actual,_extra,_tagged,
      _runtime,_positive,_activity,_parent,_node,_parentTagged,_present,_same,_edge,_leaf,
      _hidden,_hiddenFrame,_sourceChild,_sourceNode,_sourceRaw,_sourceTracker,_sourceEnabled,
      _sourceLive,_sourceTagged,_sourcePresent,_sourceSame,_sourceHidden,_sourceRuntime,
      _sourcePositive,_sourceActive,_sourceRoots,_sourceOrder,_sourceShort,_physical,
      _updatedRoots,_updatedOrder,_updatedShort⟩ :=
    S02SeparateDestinationBothPhysicalReadyInstalled.enters_ready id tag address len count input
      nonempty different returnTag returnConcrete
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
  have extras : after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) =
        some (input.contract.destination.id,⟨none,#[]⟩) := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    rw [preserved]
    exact input.return_extras
  exact ⟨installed,after.machine,actual,extras⟩

end
end DuplicatePrefix.S02SeparateDestinationZeroExtras

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationZeroExtras.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination zero-extras dependency {dependency}"
