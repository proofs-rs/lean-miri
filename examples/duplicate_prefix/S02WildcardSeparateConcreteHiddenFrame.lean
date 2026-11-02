import duplicate_prefix.S02WildcardSeparateConcreteSourceAbsent
import duplicate_prefix.S02SeparateDestinationHiddenFrame
import duplicate_prefix.S02SeparateDestinationReturnChild

namespace DuplicatePrefix.S02WildcardSeparateConcreteHiddenFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Literal return-child shape and hidden-frame packet on the same wildcard
argument/destination witnesses. No successful operation or future safety is a
premise; only the original contract and exact initial destination identity. -/
theorem written_hidden
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
        (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry output.child.tree) place)
    (entryEq : destination.entry = input.contract.destination.entry)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (returnTag : BorTag) (concrete : destination.pointer.provenance = .concrete destination.id returnTag) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
      destination.tracker returnTag destination.offset 1
    let global := TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
      (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
    ∃ parent child node,
      written.indexOfTag returnTag = some parent ∧
      written.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
      written.nodeAt child = some node ∧
      node.tag = destination.tracker.global.nextPointerTag ∧
      node.parent = some parent ∧ node.children = #[] ∧ node.isExposed = false ∧
      S04ReturnReleaseParent.HiddenFrame written
        (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
          |>.addProtector destination.id destination.tracker.global.nextPointerTag) := by
  obtain ⟨runtime,roots,order,headroom,_fresh⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh
      destination entryEq
  obtain ⟨raw,parentTag,offset,length,_selected,_maximum⟩ :=
    S03ReturnProtectionRaw.packet destination runtime roots order headroom secondFresh returnTag concrete
  obtain ⟨post,capacity,growth,postRoots,_a,_b,_c,child,tagged,⟨positive⟩,activity⟩ :=
    GeneralBorrowRawFnEntryResources.resources destination.entry.allocation.extra destination.tracker
      ({} : FrameState) destination.id runtime raw
  have postOrder := GeneralBorrowRawFnEntryOrder.order destination.entry.allocation.extra destination.tracker
    ({} : FrameState) destination.id runtime raw order
  have short : (GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
      destination.tracker raw.parentTag raw.offset raw.len).nodes.size < 65536 := by omega
  have distinct : (GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
      destination.tracker raw.parentTag raw.offset raw.len).roots.toList.Nodup := by
    rw [postRoots]; exact roots
  obtain ⟨_contract,afterRuntime,_afterPositive⟩ :=
    GeneralBorrowConcreteRowReadRange.access_runtime_kind _ _ post _ child raw.selected
      raw.maximum tagged (Size.ofBytes raw.offset) (Size.ofBytes raw.len) .Write .VisitChildrenOfAccessed
      raw.offset raw.len positive distinct (fun _ _ => postOrder) short (Nat.le_refl _) (Nat.le_refl _)
  simp only [parentTag,offset,length] at afterRuntime
  have absent := S02WildcardSeparateConcreteSourceAbsent.written address len input reference output
    firstFresh destination entryEq secondFresh returnTag concrete
  obtain ⟨parent,returnChild,node,parentTagged,returnTagged,present,same,edge,leaf,hidden⟩ :=
    S02SeparateDestinationReturnChild.run destination runtime roots order headroom secondFresh returnTag concrete
  refine ⟨afterRuntime,parent,returnChild,node,parentTagged,returnTagged,present,same,edge,leaf,hidden,?_⟩
  exact S02SeparateDestinationHiddenFrame.of_absent _ _ _ reference.id destination.id
    reference.tracker.global.nextPointerTag destination.tracker.global.nextPointerTag returnChild node rfl
    afterRuntime absent returnTagged present hidden

end
end DuplicatePrefix.S02WildcardSeparateConcreteHiddenFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateConcreteHiddenFrame.written_hidden) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard hidden-frame dependency {dependency}"
