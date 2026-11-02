import duplicate_prefix.S02SeparateDestinationPhysicalInstalled
import duplicate_prefix.S02SeparateDestinationSharedExact

namespace DuplicatePrefix.S02SeparateDestinationPacketJoin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Determinism of one actual call entry identifies the machines inside any
two successful packet builders, even if they choose different witnesses. -/
theorem same_machine (frame₁ frame₂ : CompilerFrameContext.ActualFrame)
    (machine₁ machine₂ : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (same : Storage.withCurrent #[] frame₁ machine₁ = Storage.withCurrent #[] frame₂ machine₂) :
    machine₁ = machine₂ := by
  have projected := congrArg (fun state : MachineHooks.State MiriMemoryKind Machine.RootUser => state.machine) same
  exact projected

/-- The physical destination and source-window data belong to the SAME
`Call.initStackFrame` result. No future operation result is assumed. -/
theorem source_and_physical
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
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState)
      (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (child : UniIndex)
      (_raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      Nonempty (S03FinalReturnInputBounds.Destination machine place) ∧
      machine.borrowTracker = some tracker ∧
      machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      sourceEntry = {reference.entry with allocation := (reference.entry.allocation.setExtra
        (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len))} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
        reference.offset (reference.offset+len) := by
  obtain ⟨physicalFrame,physicalMachine,physicalCall,⟨physical⟩⟩ :=
    S02SeparateDestinationPhysicalInstalled.enters id tag address len count input nonempty different
      returnTag returnConcrete
  obtain ⟨reference,tracker,frame,machine,sourceEntry,child,raw,actual,enabled,live,sourceEq,
      nextTag,parentTag,parent,offset,length,runtime,activity⟩ :=
    S02SeparateDestinationSharedExact.after_exact id tag address len count input nonempty different
      returnTag returnConcrete
  have resultEq := (EStateM.Result.ok.inj (physicalCall.symm.trans actual)).2
  have machineEq := same_machine physicalFrame frame physicalMachine machine resultEq
  rw [machineEq] at physical
  exact ⟨reference,tracker,frame,machine,sourceEntry,child,raw,actual,⟨physical⟩,
    enabled,live,sourceEq,runtime,activity⟩

end
end DuplicatePrefix.S02SeparateDestinationPacketJoin

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPacketJoin.source_and_physical) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination packet join dependency {dependency}"
