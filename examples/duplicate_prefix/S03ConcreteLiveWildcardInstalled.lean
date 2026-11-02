import duplicate_prefix.S03LiveWildcardState
import duplicate_prefix.S03LiveWildcardPostArguments
import duplicate_prefix.S03LiveEmptyContractData

namespace DuplicatePrefix.S03ConcreteLiveWildcardInstalled
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original concrete live empty argument initialization, sharing its allocation
with an original wildcard return pointer. The actual argument scope and return
protection derive the complete current packet from ConsistentContract. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete input.contract.destination.id parentTag)
    (wildcard : input.contract.destination.pointer.provenance = .wildcard)
    (count : UInt64) :
    ∃ frame machine,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer pointer) 0),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame machine) ∧
      Nonempty (S03LiveWildcardPacket.Packet options remaining span frame machine place pointer.offset.bytes count) := by
  let original := input.contract.destination
  let model := input.contract.model
  let argumentOffset := pointer.offset.bytes-original.base
  obtain ⟨nonnull,parent,parentNode,tagged,present⟩ := S03LiveEmptyContractData.parent_present input.contract parentTag argumentConcrete
  obtain ⟨runtime,distinct,order,headroom,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨dynamicFuel,validityFuel,dynamicEq,validityEq⟩ := S03LiveEmptyContractData.fuels input.contract
  let slot := ConcreteEmptyRuntimeEntry.form original.entry.allocation.extra original.tracker.global.protectedTags parentTag
    original.tracker.global.nextPointerTag runtime.formed parent parentNode tagged present
    (ConcreteEmptyRuntimeEntry.counter_fresh _ _ runtime.below)
    (by have rawRoom : original.entry.allocation.extra.nodes.size+2 < 65536 := headroom;omega)
  obtain ⟨⟨positive⟩,currentRuntime,currentOrder,roots,currentRoom,⟨zero⟩,different⟩ :=
    S03LiveEmptyState.facts original runtime first parentTag slot headroom order
  let root := RawRootInvocation.root before place model.noDataRace
  let rawMachine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete original.id original.tracker.global.nextPointerTag) (Size.ofBytes pointer.offset.bytes))
      0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted {} original.id original.tracker.global.nextPointerTag) count
  let current := S03LiveEmptyState.argumentsMachine original first parentTag slot
  let currentInput := S03LiveWildcardState.input original first parentTag slot wildcard positive
  have address : original.base+argumentOffset=pointer.offset.bytes := by
    change original.base+(pointer.offset.bytes-original.base)=pointer.offset.bytes
    rw [UInt64.add_comm,UInt64.sub_add_cancel]
  have normalized : Pointer.new (.concrete original.id parentTag) (Size.ofBytes (original.base+argumentOffset)) = pointer := by
    rw [address]
    change (⟨pointer.offset,.concrete original.id parentTag⟩ : Pointer Provenance) = pointer
    rw [←argumentConcrete]
  have initialSlot (i : Fin 25) : (root.frame.locals[i.val]'(root.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place model.noDataRace)
    have row : root.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i)).symm.trans row)
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  have arguments := ConcretePoolRootArgumentScope.scope options limits remaining span ctx model.debugOff model.nullComparator
    dynamicFuel validityFuel dynamicEq validityEq original.id parentTag original.tracker original.base argumentOffset count
    (by rw [address];exact nonnull) original.entry #[] root rawMachine
    (congrArg (fun row => row.value) (initialSlot EmptyRootArguments.i1))
    (congrArg (fun row => row.layout) (initialSlot EmptyRootArguments.i1))
    (congrArg (fun row => row.value) (initialSlot EmptyRootArguments.i2))
    (congrArg (fun row => row.layout) (initialSlot EmptyRootArguments.i2)) model.ghostOff model.shallow original.cachedBase original.live
    {} (RawRootInvocation.frame_borrow before place model.noDataRace original.tracker original.enabled)
    original.enabled first slot model.metadata input.slice_not_constructed
  have sameTracker : input.contract.tracker = original.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans original.enabled)
  have tagMargin := input.contract.resources.tagRoom
  rw [sameTracker] at tagMargin
  have firstValue := GenericFunctionEntryNumerics.successor_value original.tracker.global.nextPointerTag first
  have member : (original.id,original.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some original.live)
  have nodeMargin := input.contract.resources.nodeRoom (original.id,original.entry) member
  dsimp only at nodeMargin
  have slotGrowth := ConcreteEmptyPoolEntryNext.node_size slot
  have atMost : ConcreteEmptyPoolEntryNext.growth slot ≤ 1 := by
    cases chosen : slot.slot <;> simp only [ConcreteEmptyPoolEntryNext.growth,chosen] <;> omega
  have currentNodeRoom : currentInput.entry.allocation.extra.nodes.size+3 < 65536 := by
    change slot.after.nodes.size+3 < 65536
    omega
  have currentTagRoom : currentInput.tracker.global.nextPointerTag.value.toNat+3 < 2^64 := by
    change (TypedRetagEmpty.successorTag original.tracker.global.nextPointerTag first).value.toNat+3 < 2^64
    omega
  have currentActive : current.threads.activeThread? = some {input.contract.thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 input.contract.thread 0 input.contract.active
  obtain ⟨frame,machine,tail,packet⟩ := S03LiveWildcardPostArguments.run limits current
    (S03LiveEmptyState.model original model first parentTag slot) place currentInput currentRuntime
    (by change slot.after.roots.toList.Nodup;rw [roots];exact distinct) currentOrder currentNodeRoom second currentTagRoom wildcard
    original.tracker.global.nextPointerTag slot.index zero root (RawRootInvocation.locals before place model.noDataRace) rfl
    (RawRootInvocation.control before place model.noDataRace).2.2.1 rfl pointer.offset.bytes count
    input.return_extras input.slice_not_constructed {input.contract.thread with topUserRelevantFrame := some 0} currentActive rfl
  change RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
    (Storage.withCurrent #[] args.frame current) = .ok () (Storage.withCurrent #[] frame machine) at tail
  simp only [args,adjusted,←address] at tail
  have entry : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete original.id parentTag) (Size.ofBytes (original.base+argumentOffset))) 0 ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) := by
    have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits model.debugOff
      (⟨⟨#[]⟩,before⟩ : RootState) (.memory place) input.contract.thread input.contract.active input.contract.emptyHarnessCache
    have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] root.frame rawMachine
    have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] root.frame root.frame rawMachine
    have control := RawRootInvocation.control before place model.noDataRace
    have preamble : root.frame.location = .unwinding ⟨559⟩ := control.1
    have unchanged : {root.frame with trackCallerArg := none} = root.frame := by rw [←control.2.1]
    simp only [preamble] at unchanged
    rw [RootCallCore.actual_entry_eq]
    unfold RootCallCore.core
    simp only [bind,EStateM.bind]
    unfold CallEntryFacts.config at push
    rw [push,RawRootInvocation.raw_eq #[] before place model.noDataRace]
    simp only [EStateM.bind]
    rw [getFrame]
    simp only [EStateM.bind,preamble,pure,EStateM.pure]
    rw [unchanged,setFrame]
    simp only [EStateM.bind]
    rw [arguments]
    simp only [EStateM.bind]
    exact tail
  refine ⟨frame,machine,?_,packet⟩
  simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,normalized] using entry

end
end DuplicatePrefix.S03ConcreteLiveWildcardInstalled
