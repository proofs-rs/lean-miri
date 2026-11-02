import duplicate_prefix.S05ConcreteEntryBridge
import duplicate_prefix.S05ConsistentCallSpecification
import duplicate_prefix.GeneralBorrowRawFnEntryScope
import duplicate_prefix.RawRootInvocation

namespace DuplicatePrefix.S02ConcreteArgumentScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext RootFrameData DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- On the exact raw frame pushed for the original call, both typed argument
passes execute for a positive concrete slice. The result state is the one
formed by the real FnEntry Read/constructor and the count argument. This does
not yet execute return-place protection or finish `initStackFrame`. -/
theorem argument_body
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      (ExecutionMachine.callHooks cfg limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks cfg limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result
            (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
              reference.id reference.tracker.global.nextPointerTag) count).frame
          (GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
            reference.id reference.entry tag reference.offset len)) := by
  obtain ⟨reference,same,raw,parentTag,offset,length,_,_,_,runtime⟩ :=
    S05ConcreteEntryBridge.from_contract id tag address len input.contract nonempty
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let machine := RawRootInvocation.machine #[] before
  have fields := RawRootInvocation.preservation #[] before
  obtain ⟨memory,borrow,race,addresses,ghost,shallow,types,backend,extras⟩ := fields
  have dead (i : Fin 25) : (root.frame.locals[i.val]'(root.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place input.contract.model.noDataRace)
    have row : root.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i)).symm.trans row)
  have frameBorrow := RawRootInvocation.frame_borrow before place input.contract.model.noDataRace
    reference.tracker reference.enabled
  have positive : (0 : UInt64) < len := UInt64.lt_iff_toNat_lt.mpr reference.storage.positive
  have bounds : reference.offset.toNat + len.toNat ≤ reference.entry.allocation.byteSize.bytes.toNat := by
    simpa only [reference.size,Size.ofBytes] using reference.storage.bounds
  have capacity : reference.entry.allocation.extra.locations.size = reference.entry.allocation.byteSize := by
    calc
      reference.entry.allocation.extra.locations.size =
          Size.ofBytes reference.entry.allocation.extra.locations.size.bytes := by
            cases reference.entry.allocation.extra.locations.size; rfl
      _ = Size.ofBytes reference.capacity := congrArg Size.ofBytes reference.borrowSize
      _ = reference.entry.allocation.byteSize := reference.size.symm
  have initialWork : 64 ≤ work before len := by unfold work;omega
  have dynamicEq : options.place.dynamicFuel = (options.place.dynamicFuel-1)+1 := by
    have room := input.contract.resources.dynamicFuel
    omega
  have validityEq : options.limits.validation = (options.limits.validation-1)+1 := by
    have room := input.contract.resources.configuredFuel.2.2.2
    omega
  have sourceAddress : address = reference.base+reference.offset := reference.pointerAddress
  have normalized : (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address) : Pointer Provenance) =
      Pointer.new (Provenance.concrete reference.id tag) (Size.ofBytes (reference.base+reference.offset)) := by
    simp only [same,sourceAddress]
  have nonnull : reference.base+reference.offset ≠ 0 := by
    rw [←sourceAddress]
    exact reference.nonnull
  let ctx := Classical.choice (DuplicatePrefixCallModel.contexts options remaining span before input.contract.model).1
  have passed := GeneralBorrowRawFnEntryScope.scope options limits remaining span ctx
    input.contract.model.debugOff input.contract.model.nullComparator
    (options.place.dynamicFuel-1) (options.limits.validation-1) dynamicEq validityEq
    reference.id tag reference.tracker reference.base reference.offset len count nonnull
    reference.entry positive reference.storage.signedSize bounds #[] root machine
    (congrArg (fun row => row.value) (dead EmptyRootArguments.i1))
    (congrArg (fun row => row.layout) (dead EmptyRootArguments.i1))
    (congrArg (fun row => row.value) (dead EmptyRootArguments.i2))
    (congrArg (fun row => row.layout) (dead EmptyRootArguments.i2))
    (ghost.trans input.contract.model.ghostOff) (shallow.trans input.contract.model.shallow)
    (by rw [addresses];exact reference.cachedBase)
    (by rw [memory];exact reference.live)
    {} frameBorrow (borrow.trans reference.enabled) raw.tagRoom runtime raw parentTag offset length
    capacity (race.trans input.contract.model.noDataRace)
    (by rw [types];exact input.contract.model.metadata)
    (by rw [types];exact input.slice_not_constructed)
  refine ⟨reference,raw.tagRoom,?_⟩
  simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,normalized,
    root,machine] using passed

end
end DuplicatePrefix.S02ConcreteArgumentScope
