import duplicate_prefix.S02SeparateDestinationSharedExact
import duplicate_prefix.GeneralBorrowRawFnEntryResources

namespace DuplicatePrefix.S02InstalledResourceMargin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The real initial call consumes two global tags (source and destination),
while its source allocation grows by at most one node. The original resource
budget leaves fourteen global tags and fifteen source nodes available to the
shared/Default suffix; no intermediate resource or success condition is input. -/
theorem after_concrete
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
      (tracker : MachineHooks.BorrowState) (installed : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post) ∧
      post.borrowTracker = some tracker ∧
      post.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      sourceEntry.allocation.extra.nodes.size + 15 < 65536 ∧
      tracker.global.nextPointerTag.value.toNat + 14 < 2^64 ∧
      tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat + 2 := by
  obtain ⟨reference,tracker,installed,post,sourceEntry,child,shared,actual,tracked,live,sourceEq,counter,rest⟩ :=
    S02SeparateDestinationSharedExact.after_exact id tag address len count input nonempty different returnTag returnConcrete
  obtain ⟨_,raw,parent,offset,length,_,_,_,runtime⟩ := S05ConcreteEntryBridge.from_positive
    id tag address len reference input.contract.runtime input.contract.resources
  obtain ⟨_,capacity,growth,rest⟩ := GeneralBorrowRawFnEntryResources.resources
    reference.entry.allocation.extra reference.tracker {} reference.id runtime raw
  have sourceGrowth : sourceEntry.allocation.extra.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 := by
    rw [sourceEq]
    change (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker
      tag reference.offset len).nodes.size ≤ _
    simpa only [parent,offset,length] using growth
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have nodes := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  have trackerEq : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have tags := input.contract.resources.tagRoom
  rw [←trackerEq] at tags
  refine ⟨reference,tracker,installed,post,sourceEntry,actual,tracked,live,?_,?_,counter⟩
  · dsimp only at nodes
    omega
  · omega

end
end DuplicatePrefix.S02InstalledResourceMargin
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02InstalledResourceMargin.after_concrete) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
