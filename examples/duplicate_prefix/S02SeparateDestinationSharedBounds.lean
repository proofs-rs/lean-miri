import duplicate_prefix.S02SeparateDestinationSharedExact
import duplicate_prefix.S05ConcreteEntryBridge
import duplicate_prefix.GeneralBorrowRawFnEntryResources

namespace DuplicatePrefix.S02SeparateDestinationSharedBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The source allocation selected by the actual call meets every numeric and
storage prerequisite of the shared-Ref/len path. The equality and counter are
conclusions of SharedExact; they are not additional caller restrictions. -/
theorem of_exact_source
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceEq : sourceEntry = {reference.entry with allocation := (reference.entry.allocation.setExtra
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len))})
    (tracker : MachineHooks.BorrowState)
    (counter : tracker.global.nextPointerTag.value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 2) :
    (0 : UInt64) < len ∧
    reference.base + reference.offset ≠ 0 ∧
    len.toNat < 9223372036854775808 ∧
    reference.offset.toNat + len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat ∧
    sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize ∧
    sourceEntry.allocation.extra.nodes.size + 2 < 65536 ∧
    sourceEntry.allocation.extra.nodes.size + 2 ≤ 4294967295 ∧
    tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615 := by
  obtain ⟨_same,raw,parent,offset,length,_source,_selected,_maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference
      input.contract.runtime input.contract.resources
  obtain ⟨_afterRuntime,capacity,growth,_roots,_held,_frame,_fresh,_child,_tagged,_positive,_active⟩ :=
    GeneralBorrowRawFnEntryResources.resources reference.entry.allocation.extra reference.tracker
      {} reference.id runtime raw
  have treeEq : GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len =
      GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker
        raw.parentTag raw.offset raw.len := by
    rw [parent,offset,length]
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have treeLength : reference.entry.allocation.extra.locations.size = reference.entry.allocation.byteSize :=
    input.contract.runtime.treeLength (reference.id,reference.entry) member
  have room : reference.entry.allocation.extra.nodes.size + 16 < 65536 := by
    simpa only [Prod.snd] using input.contract.resources.nodeRoom (reference.id,reference.entry) member
  have refTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have tagMargin : reference.tracker.global.nextPointerTag.value.toNat + 16 < 18446744073709551616 := by
    rw [refTracker]
    exact input.contract.resources.tagRoom
  have sourceNodes : sourceEntry.allocation.extra.nodes.size ≤ reference.entry.allocation.extra.nodes.size + 1 := by
    rw [sourceEq]
    change (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len).nodes.size ≤ _
    rw [treeEq]
    exact growth
  have sourceCapacity : sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize := by
    rw [sourceEq]
    change (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len).locations.size = reference.entry.allocation.byteSize
    rw [treeEq]
    exact capacity.trans treeLength
  have bounds : reference.offset.toNat + len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat := by
    rw [sourceEq]
    change reference.offset.toNat + len.toNat ≤ reference.entry.allocation.byteSize.bytes.toNat
    rw [reference.size]
    simpa only [Size.ofBytes] using reference.storage.bounds
  refine ⟨?_,?_,reference.storage.signedSize,bounds,sourceCapacity,?_,?_,?_⟩
  · apply UInt64.lt_iff_toNat_lt.mpr
    change 0 < len.toNat
    exact reference.storage.positive
  · rw [←reference.pointerAddress]
    exact reference.nonnull
  · omega
  · omega
  · omega

end
end DuplicatePrefix.S02SeparateDestinationSharedBounds

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSharedBounds.of_exact_source) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate shared bounds dependency {dependency}"
