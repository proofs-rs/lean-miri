import duplicate_prefix.S02WildcardSameDestinationInitReady
import duplicate_prefix.S02WildcardSameDestinationRootOperation
namespace DuplicatePrefix.S02WildcardSameDestinationInitAfterArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Current return input and actual source root on the same post-argument
allocation. All facts precede return protection; none assumes its success. -/
structure Ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) (returnTag : BorTag) where
  destination : DuplicatePrefixReturnPlaceInput.Input
    (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker fresh reference.id reference.entry output.child.tree) place
  sameId : destination.id = reference.id
  offset : destination.offset = input.contract.destination.offset
  concrete : destination.pointer.provenance = .concrete destination.id returnTag
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra destination.tracker.global
  distinct : destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra
  headroom : destination.entry.allocation.extra.nodes.size+1 < 65536
  nextFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615
  child : UniIndex
  node : TreeNode
  tagged : destination.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some child
  present : destination.entry.allocation.extra.nodeAt child = some node
  tag : node.tag = reference.tracker.global.nextPointerTag
  leaf : node.children = #[]
  hidden : node.isExposed = false
  positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra destination.tracker.global.protectedTags
    (some child) (some child) (some reference.tracker.global.nextPointerTag) reference.offset len
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra child .Write reference.offset (reference.offset+len)
  notSourceParent : destination.source ≠ some child
  disjoint : destination.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ destination.offset.toNat

/-- Actual typed wildcard FnEntry preserves the disjoint concrete return
owner through its Read and fresh parentless root constructor. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra reference.tracker.global
        ({} : FrameState) reference.id reference.offset len = .ok output ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len) (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) = .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
            reference.id reference.tracker.global.nextPointerTag) count).frame current) ∧
      (reference.id = input.contract.destination.id → Nonempty (Ready input reference output fresh returnTag)) := by
  obtain ⟨reference,output,fresh,run,argument⟩ := S02WildcardArgumentScope.argument_body address len count input nonempty
  refine ⟨reference,output,fresh,run,argument,?_⟩
  intro same
  let original := input.contract.destination
  have entryEq : reference.entry = original.entry := by
    have live := reference.live
    rw [same] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans original.live))
  have trackerEq : original.tracker = reference.tracker := Option.some.inj (original.enabled.symm.trans reference.enabled)
  obtain ⟨_,_,_,sourcePositive,initialRuntime,initialDistinct,initialShort,initialRoom,initialFresh⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState input.contract.resources
  have destinationPositive : DuplicatePrefixBorrowAuthorization.Positive reference.entry.allocation.extra reference.tracker.global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1 := by
    rw [entryEq,←trackerEq];exact original.borrow
  have separation := S02WildcardSameDestinationInitInput.disjoint address len input nonempty reference same
  have endFit : original.offset.toNat+1 < 2^64 := by
    have bounds := original.bounds
    have fits := original.capacity.toNat_lt
    omega
  have endNat : (original.offset+1).toNat = original.offset.toNat+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endFit]
  have outside : reference.offset.toNat+len.toNat ≤ original.offset.toNat ∨ (original.offset+1).toNat ≤ reference.offset.toNat := by
    simpa only [original,endNat] using separation
  obtain ⟨other,otherRun,⟨destinationAfter⟩,capacity,oldNodes,oldTags⟩ :=
    S02WildcardSameDestinationRootOperation.operation_destination reference.entry.allocation.extra reference.tracker.global
      ({} : FrameState) reference.id initialRuntime reference.offset len sourcePositive initialDistinct initialShort initialRoom initialFresh
      original.source original.selectedRoot original.maximum original.offset 1 outside destinationPositive
  have sameOutput : other = output := Except.ok.inj (otherRun.symm.trans run)
  subst other
  obtain ⟨runtime,distinct,order,headroom,nextFresh,_capacity,child,node,tagged,present,tag,parent,leaf,hidden,
    ⟨positive⟩,activity,globalEq⟩ := S02WildcardSameDestinationInitReady.facts address len input reference output fresh run
  rw [globalEq] at destinationAfter
  let destination := S02WildcardSameDestinationInitInput.at_current input reference fresh same returnTag returnConcrete
    output.child.tree capacity oldTags destinationAfter
  have notSourceParent : destination.source ≠ some child := by
    have binding := original.binding
    have concrete : original.pointer.provenance = .concrete original.id returnTag := returnConcrete
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    obtain ⟨_,parentIndex,parentSource,parentTagged⟩ := binding
    obtain ⟨oldNode,oldPresent⟩ := original.borrow.sourcePresent parentIndex parentSource
    have beforePresent : reference.entry.allocation.extra.nodeAt parentIndex = some oldNode := by rw [entryEq];exact oldPresent
    have afterPresent := oldNodes parentIndex oldNode beforePresent
    have below := GeneralBorrowForestTagHighWater.mapped reference.entry.allocation.extra reference.tracker.global.protectedTags
      reference.tracker.global.nextPointerTag oldNode.tag initialRuntime.below parentIndex
      (initialRuntime.formed.allocator.nodeTags parentIndex oldNode beforePresent)
    intro equal
    have oldSame : parentIndex = child := Option.some.inj (parentSource.symm.trans equal)
    rw [oldSame] at afterPresent
    have nodeEq : oldNode = node := Option.some.inj (afterPresent.symm.trans present)
    have sameTag : oldNode.tag = reference.tracker.global.nextPointerTag := (congrArg TreeNode.tag nodeEq).trans tag
    rw [sameTag] at below
    omega
  have sourceEnd : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt sourcePositive.bounds reference.entry.allocation.extra.locations.size.bytes.toNat_lt
  exact ⟨{
    destination := destination,sameId := same.symm,offset := rfl,concrete := returnConcrete,
    runtime := runtime,distinct := distinct,order := order,headroom := headroom,nextFresh := nextFresh,
    child := child,node := node,tagged := tagged,present := present,tag := tag,leaf := leaf,hidden := hidden,
    positive := positive,activity := activity,notSourceParent := notSourceParent,
    disjoint := by change original.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ original.offset.toNat
                   rw [sourceEnd];exact separation.symm }⟩
end
end DuplicatePrefix.S02WildcardSameDestinationInitAfterArgument
