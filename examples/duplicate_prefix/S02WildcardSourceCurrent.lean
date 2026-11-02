import duplicate_prefix.S02WildcardSeparateDestinationInput
import duplicate_prefix.S05WildcardEntryBridge
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryResources

namespace DuplicatePrefix.S02WildcardSourceCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The post-argument source row and full protected wildcard-root capability
share the same actual witness as a distinct return-place Input. -/
theorem current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      (ExecutionMachine.callHooks cfg limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks cfg limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result
            (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
              reference.id reference.tracker.global.nextPointerTag) count).frame current) ∧
      (reference.id ≠ input.contract.destination.id →
        ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
          (child : UniIndex) (node : TreeNode),
          destination.id = input.contract.destination.id ∧
          current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
          sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some child ∧
          sourceEntry.allocation.extra.nodeAt child = some node ∧
          node.tag = reference.tracker.global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false ∧
          DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra destination.tracker.global ∧
          Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
            destination.tracker.global.protectedTags (some child) (some child)
            (some reference.tracker.global.nextPointerTag) reference.offset len) ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
            reference.offset (reference.offset+len)) := by
  obtain ⟨reference,output,fresh,run,argument,destReady⟩ :=
    S02WildcardSeparateDestinationInput.destination_input_after_argument address len count input nonempty
  obtain ⟨_,_,_,capability,runtime,distinct,short,nodeRoom,_⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState
      input.contract.resources
  obtain ⟨constructed,created,tagEq,globalEq,_frameEq,_access,_childDone,afterRuntime,_capacity,
    _growth,child,lookup,_roots,positive,activity,node,present,nodeTag,parent,children,hidden⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke reference.entry.allocation.extra
      reference.tracker.global {} reference.id runtime reference.offset len capability distinct short
      nodeRoom fresh
  have same : constructed = output := Except.ok.inj (created.symm.trans run)
  subst constructed
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
    (RawRootInvocation.machine #[] before) reference.tracker fresh reference.id reference.entry output.child.tree
  refine ⟨reference,output,fresh,argument,?_⟩
  intro different
  obtain ⟨destination,destId,_destEntry,_destOffset⟩ := destReady different
  have sourceLive : current.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory reference.id
      reference.entry output.child.tree).live.find? (fun row => row.1 == reference.id) = _
    exact MemoryCopyBridge.live_lookup_replaced _ reference.id sourceEntry
  have globalCurrent : destination.tracker.global = output.global := by
    have h := destination.enabled.symm
    change some destination.tracker = some
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩ at h
    have eq := congrArg MachineHooks.BorrowState.global (Option.some.inj h)
    rw [globalEq]
    exact eq
  refine ⟨destination,child,node,destId,sourceLive,?_,?_,?_,parent,children,hidden,?_,?_,?_⟩
  · change output.child.tree.indexOfTag reference.tracker.global.nextPointerTag = some child
    simpa only [tagEq] using lookup
  · change output.child.tree.nodeAt child = some node
    exact present
  · simpa only [tagEq] using nodeTag
  · change DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree destination.tracker.global
    rw [globalCurrent]
    exact afterRuntime
  · change Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree
      destination.tracker.global.protectedTags (some child) (some child)
      (some reference.tracker.global.nextPointerTag) reference.offset len)
    rw [globalCurrent]
    simpa only [tagEq] using positive
  · change GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write
      reference.offset (reference.offset+len)
    exact activity

end
end DuplicatePrefix.S02WildcardSourceCurrent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceCurrent.current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard current-source dependency {dependency}"
