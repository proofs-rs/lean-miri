import duplicate_prefix.S02WildcardReturnSameCountEntry
import duplicate_prefix.S02WildcardFinishFromProtect
import duplicate_prefix.S02WildcardSameDestinationInitReady
import duplicate_prefix.S02WildcardSameDestinationRootOperation
namespace DuplicatePrefix.S02WildcardSourceWildcardSameInitial
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
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) where
  destination : DuplicatePrefixReturnPlaceInput.Input
    (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker fresh reference.id reference.entry output.child.tree) place
  sameId : destination.id = reference.id
  offset : destination.offset = input.contract.destination.offset
  wildcard : destination.pointer.provenance = .wildcard
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
  parentless : node.parent = none
  nodeReserve : destination.entry.allocation.extra.nodes.size+14 < 65536
  tagReserve : destination.tracker.global.nextPointerTag.value.toNat+14 < 18446744073709551615
  disjoint : destination.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ destination.offset.toNat

/-- Actual typed wildcard FnEntry preserves the disjoint wildcard return
owner through its Read and fresh parentless root constructor. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
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
      (reference.id = input.contract.destination.id → Nonempty (Ready input reference output fresh)) := by
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
  let destination : DuplicatePrefixReturnPlaceInput.Input (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before) reference.tracker fresh reference.id reference.entry output.child.tree) place := {
    tracker := ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩,enabled := rfl,
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := {original.entry with allocation := original.entry.allocation.setExtra output.child.tree},
    base := original.base,offset := original.offset,capacity := original.capacity,
    live := by
      change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory reference.id reference.entry output.child.tree).live.find? (fun row => row.1 == original.id) = _
      rw [←same,←entryEq];exact MemoryCopyBridge.live_lookup_replaced _ _ _,
    cachedBase := by
      change (RawRootInvocation.machine #[] before).user.addresses.baseAddr.find? (fun row => row.allocId == original.id) = _
      rw [(RawRootInvocation.preservation #[] before).2.2.2.1];exact original.cachedBase,
    pointerAddress := original.pointerAddress,nonnull := original.nonnull,addressFits := original.addressFits,bounds := original.bounds,
    size := original.size,bytes := original.bytes,mutable := original.mutable,maskValid := original.maskValid,maskLength := original.maskLength,
    provenanceMap := original.provenanceMap,borrowSize := by change output.child.tree.locations.size.bytes = original.capacity;rw [capacity,entryEq];exact original.borrowSize,
    source := original.source,selectedRoot := original.selectedRoot,maximum := original.maximum,
    binding := by
      change DuplicatePrefixReferenceInput.Binding (RawRootInvocation.machine #[] before).user.addresses original.pointer original.id original.base _ _ original.source
      have bind := original.binding
      simp only [DuplicatePrefixReferenceInput.Binding,show original.pointer.provenance = .wildcard from returnWildcard] at bind ⊢
      rw [(RawRootInvocation.preservation #[] before).2.2.2.1]
      exact bind,
    borrow := destinationAfter }
  have sourceEnd : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt sourcePositive.bounds reference.entry.allocation.extra.locations.size.bytes.toNat_lt
  refine ⟨{
    destination := destination,sameId := same.symm,offset := rfl,wildcard := returnWildcard,
    runtime := runtime,distinct := distinct,order := order,headroom := headroom,nextFresh := nextFresh,
    child := child,node := node,tagged := tagged,present := present,tag := tag,leaf := leaf,hidden := hidden,
    positive := positive,activity := activity,parentless := parent,nodeReserve := ?_,tagReserve := ?_,
    disjoint := by change original.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ original.offset.toNat
                   rw [sourceEnd];exact separation.symm }⟩
  · have member : (reference.id,reference.entry) ∈ before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
    have margin := input.contract.resources.nodeRoom (reference.id,reference.entry) member
    obtain ⟨created,createdRun,_,_,_,_,_,_,_,growth,_⟩ := GeneralBorrowRawWildcardFnEntryResources.invoke
      reference.entry.allocation.extra reference.tracker.global ({} : FrameState) reference.id initialRuntime reference.offset len
      sourcePositive initialDistinct initialShort initialRoom initialFresh
    have eq : created = output := Except.ok.inj (createdRun.symm.trans run)
    subst created
    change output.child.tree.nodes.size+14 < 65536
    change reference.entry.allocation.extra.nodes.size+16 < 65536 at margin
    omega
  · have refTracker : reference.tracker = input.contract.tracker := Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
    have reserve : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by rw [refTracker];exact input.contract.resources.tagRoom
    have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag fresh
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag fresh).value.toNat+14 < 18446744073709551615
    omega

/-- The actual arbitrary-count call installs the source and parentless wildcard
return owner; the reserved margins follow from the unchanged contract. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output) (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      reference.id = input.contract.destination.id →
      ∃ data : Ready input reference output fresh,
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker fresh reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      let changed := {(RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted {} reference.id reference.tracker.global.nextPointerTag) count).frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      ∃ post : S02WildcardReturnSameCountEntry.Packet options (remaining+1) span limits.retag current place data.destination
        #[] changed owned data.nextFresh reference.tracker.global.nextPointerTag data.child data.child (some reference.tracker.global.nextPointerTag) reference.offset len data.node,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
        false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[]
          (CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame changed owned data.destination.id data.destination.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩})
          (S04ProtectUninit.finished current place data.destination #[] changed owned data.nextFresh post.tree post.updated).machine) ∧
      post.updated.extra.nodes.size+8 < 65536 ∧
      (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker data.destination.tracker data.nextFresh)
        data.destination.tracker.global.nextPointerTag).nextPointerTag.value.toNat+7 < 18446744073709551615 := by
  obtain ⟨reference,output,fresh,run,argument,available⟩ := ready address len count input nonempty returnWildcard
  refine ⟨reference,output,fresh,?_⟩
  intro same
  obtain ⟨data⟩ := available same
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker fresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let changed := {(RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted {} reference.id reference.tracker.global.nextPointerTag) count).frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == data.destination.id) = some (data.destination.id,⟨none,#[]⟩) := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find? _ = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,data.sameId,same];exact input.return_extras
  obtain ⟨post⟩ := S02WildcardReturnSameCountEntry.after_current (options := options) (remaining := remaining+1) (span := span)
    limits.retag current (S02WildcardSeparateDestinationReady.model_after_argument input reference output fresh) place data.destination
    data.runtime data.distinct data.order data.headroom data.nextFresh data.wildcard #[] changed owned frameBorrow #[] extras (by simp)
    reference.tracker.global.nextPointerTag data.child data.child (some reference.tracker.global.nextPointerTag) reference.offset len data.node
    data.tagged data.present data.leaf data.hidden data.disjoint data.positive data.activity
  refine ⟨data,post,S02WildcardFinishFromProtect.init address len count input nonempty reference output fresh argument
    data.destination data.nextFresh post.tree post.updated post.protect,?_,?_⟩
  · have reserve := data.nodeReserve;have growth := post.growth;omega
  · have reserve := data.tagReserve
    have successor := GenericFunctionEntryNumerics.successor_value data.destination.tracker.global.nextPointerTag data.nextFresh
    change (TypedRetagEmpty.successorTag data.destination.tracker.global.nextPointerTag data.nextFresh).value.toNat+7 < 18446744073709551615
    omega

end
end DuplicatePrefix.S02WildcardSourceWildcardSameInitial

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardSourceWildcardSameInitial." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved wildcard same Initial dependency {dependency}"
