import duplicate_prefix.S02SameDestinationInput
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02FnEntryOldNode

namespace DuplicatePrefix.S02SameDestinationSourceParent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The original return parent cannot be the fresh source leaf. The original
parent was already present before source construction and keeps its older tag;
this excludes aliasing even for arbitrary multi-root and reused-slot graphs. -/
theorem separate
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (sameAllocation : id = input.contract.destination.id)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before) reference.tracker fresh
        reference.id reference.entry tag reference.offset len) place)
    (returnTag : BorTag) (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (sourceChild : UniIndex) (sourceNode : TreeNode)
    (sourcePresent : destination.entry.allocation.extra.nodeAt sourceChild = some sourceNode)
    (sourceTag : sourceNode.tag = reference.tracker.global.nextPointerTag) :
    ∃ parent,destination.source = some parent ∧ destination.entry.allocation.extra.indexOfTag returnTag = some parent ∧ sourceChild ≠ parent := by
  obtain ⟨idEq,raw,parentTag,offsetEq,lenEq,_source,_selected,_maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference input.contract.runtime input.contract.resources
  have refId : reference.id = input.contract.destination.id := idEq.symm.trans sameAllocation
  have originalEntry : reference.entry = input.contract.destination.entry := by
    have live := reference.live
    rw [refId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans input.contract.destination.live))
  have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
  have prov := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
  simp only [Pointer.withOptionalProvenance] at prov
  have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
    (Option.some.inj prov).trans returnConcrete
  have binding := destination.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨destId,parent,destSource,destTagged⟩ := binding
  have sameId : destination.id = reference.id := destId.symm.trans refId.symm
  obtain ⟨_child,_raw,_id,_parent,_offset,_len,sourceLive,_enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference fresh
  have entryEq : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len)} := by
    have live := destination.live
    rw [sameId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans sourceLive))
  have originalBinding := input.contract.destination.binding
  simp only [DuplicatePrefixReferenceInput.Binding,returnConcrete] at originalBinding
  obtain ⟨_,originalParent,originalSource,originalTagged⟩ := originalBinding
  obtain ⟨oldNode,oldPresent⟩ := input.contract.destination.borrow.sourcePresent originalParent originalSource
  have oldTagged : reference.entry.allocation.extra.indexOfTag returnTag = some originalParent := by
    rw [originalEntry];exact originalTagged
  have beforePresent : reference.entry.allocation.extra.nodeAt originalParent = some oldNode := by
    rw [originalEntry];exact oldPresent
  have mapped := S02FnEntryBinding.mapped reference.entry.allocation.extra reference.tracker ({} : FrameState) reference.id runtime raw
    returnTag originalParent oldTagged
  obtain ⟨next,nextPresent,nextTag,_exposed⟩ := S02FnEntryOldNode.preserved reference.entry.allocation.extra reference.tracker
    ({} : FrameState) reference.id runtime raw originalParent oldNode beforePresent
  simp only [parentTag,offsetEq,lenEq] at mapped nextPresent
  have destTree : destination.entry.allocation.extra =
      GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len := by rw [entryEq];rfl
  rw [←destTree] at mapped nextPresent
  have parentEq : originalParent = parent := Option.some.inj (mapped.symm.trans destTagged)
  have below := GeneralBorrowForestTagHighWater.mapped reference.entry.allocation.extra reference.tracker.global.protectedTags
    reference.tracker.global.nextPointerTag oldNode.tag runtime.below originalParent
    (runtime.formed.allocator.nodeTags originalParent oldNode beforePresent)
  refine ⟨parent,destSource,destTagged,?_⟩
  intro same
  rw [same,←parentEq] at sourcePresent
  have sameNode : sourceNode = next := Option.some.inj (sourcePresent.symm.trans nextPresent)
  have sameTag : reference.tracker.global.nextPointerTag = oldNode.tag := sourceTag.symm.trans ((congrArg TreeNode.tag sameNode).trans nextTag)
  rw [sameTag] at below
  omega

end
end DuplicatePrefix.S02SameDestinationSourceParent

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationSourceParent.separate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
