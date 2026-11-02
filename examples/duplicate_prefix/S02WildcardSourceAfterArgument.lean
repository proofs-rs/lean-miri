import duplicate_prefix.S02WildcardArgumentScope
import duplicate_prefix.S05WildcardEntryBridge
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryResources

namespace DuplicatePrefix.S02WildcardSourceAfterArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual wildcard FnEntry argument result carries the same protected
fresh root produced by the raw operation, with full Both capability, bounded
Write activity and a hidden child. No return-place step is assumed here. -/
theorem formed
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
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry output.child.tree
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
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
      ∃ child node,
        output.tag = reference.tracker.global.nextPointerTag ∧
        output.global = (GeneralBorrowFnEntryRegistration.registered reference.tracker.global
          ({} : FrameState) reference.id fresh).1 ∧
        DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
        output.child.tree.indexOfTag reference.tracker.global.nextPointerTag = some child ∧
        output.child.tree.nodeAt child = some node ∧
        node.tag = reference.tracker.global.nextPointerTag ∧
        node.parent = none ∧ node.children = #[] ∧ node.isExposed = false ∧
        output.child.tree.roots = reference.entry.allocation.extra.roots.push child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some child) (some output.tag) reference.offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write
          reference.offset (reference.offset+len) := by
  obtain ⟨reference,output,fresh,run,actual⟩ :=
    S02WildcardArgumentScope.argument_body address len count input nonempty
  obtain ⟨_,_,_,capability,runtime,distinct,short,nodeRoom,_⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState
      input.contract.resources
  obtain ⟨constructed,created,tagEq,globalEq,_frameEq,_access,_childDone,afterRuntime,_capacity,
    _growth,child,lookup,roots,positive,activity,node,present,nodeTag,parent,children,hidden⟩ :=
    GeneralBorrowRawWildcardFnEntryResources.invoke reference.entry.allocation.extra
      reference.tracker.global {} reference.id runtime reference.offset len capability distinct short
      nodeRoom fresh
  have same : constructed = output := Except.ok.inj (created.symm.trans run)
  subst constructed
  exact ⟨reference,output,fresh,actual,child,node,tagEq,globalEq,afterRuntime,
    by simpa only [tagEq] using lookup,present,by simpa only [tagEq] using nodeTag,
    parent,children,hidden,roots,positive,activity⟩

end
end DuplicatePrefix.S02WildcardSourceAfterArgument

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceAfterArgument.formed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard source-after-argument dependency {dependency}"
