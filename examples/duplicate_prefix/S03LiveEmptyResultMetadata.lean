import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S03LiveEmptyResultMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Allocation identity in the exact installed state identifies its physical
result, independently of the intermediate protected tree. -/
theorem allocation_eq {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (leftTree rightTree : BorrowTree) (left right : Allocation Provenance BorrowTree)
    (same : S04ProtectUninit.finished before place input frames frame borrowFrame fresh leftTree left =
      S04ProtectUninit.finished before place input frames frame borrowFrame fresh rightTree right) : left = right := by
  have found := congrArg (fun state : RootState => state.machine.memory.live.find? (fun row => row.1 == input.id)) same
  have leftLive : (S04ProtectUninit.finished before place input frames frame borrowFrame fresh leftTree left).machine.memory.live.find?
      (fun row => row.1 == input.id) = some (input.id,{input.entry with allocation := left}) :=
    MemoryCopyBridge.live_lookup_replaced _ input.id _
  have rightLive : (S04ProtectUninit.finished before place input frames frame borrowFrame fresh rightTree right).machine.memory.live.find?
      (fun row => row.1 == input.id) = some (input.id,{input.entry with allocation := right}) :=
    MemoryCopyBridge.live_lookup_replaced _ input.id _
  rw [leftLive,rightLive] at found
  exact congrArg (fun row => row.2.allocation) (Option.some.inj found)

/-- Metadata of the physical allocation returned by a derived actual
protect+uninit equation. This helper is consumed after actual execution is
proved; its enclosing call theorem assumes no completed operation. -/
theorem physical
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) = some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync, row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (actual : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
      (Storage.withCurrent frames frame before) =
      .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated)) :
    InitMaskCopy.WellFormed updated.initializationMask ∧
    updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
    (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) := by
  obtain ⟨result,computed,_,_,_,_,mask,length,pointers,_⟩ :=
    S03ReturnProtectionMetadata.invoke_concrete budget before model place input runtime distinct order headroom fresh tag concrete
      frames frame borrowFrame frameBorrow sync extras outside
  have states := (EStateM.Result.ok.inj (actual.symm.trans computed)).2
  have same := allocation_eq input frames frame borrowFrame fresh tree _ updated result states
  subst result
  exact ⟨mask,length,pointers⟩

end
end DuplicatePrefix.S03LiveEmptyResultMetadata
