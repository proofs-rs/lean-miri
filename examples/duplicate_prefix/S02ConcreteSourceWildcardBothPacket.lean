import duplicate_prefix.S02ConcreteSourceWildcardReturnPacket
import duplicate_prefix.S02SeparateDestinationSourceFullAtWitness

namespace DuplicatePrefix.S02ConcreteSourceWildcardBothPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The source part of the exact wildcard-return protector state. -/
structure SourcePacket
    {before : Before} (id : AllocId) (tag : BorTag) (address len : UInt64)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global
  child : UniIndex
  node : TreeNode
  tracker : MachineHooks.BorrowState
  enabled : machine.borrowTracker = some tracker
  live : machine.memory.live.find? (fun row => row.1 == reference.id) =
    some (reference.id,{reference.entry with allocation := (reference.entry.allocation.setExtra
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len))})
  tagged : (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len).indexOfTag reference.tracker.global.nextPointerTag = some child
  present : (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len).nodeAt child = some node
  same : node.tag = reference.tracker.global.nextPointerTag
  hidden : node.isExposed = false
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts
    (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len) tracker.global
  positive : DuplicatePrefixBorrowAuthorization.Positive
    (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len) tracker.global.protectedTags
      (some child) (some raw.selected) raw.maximum reference.offset len
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin
    (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len) child .Write
      reference.offset (reference.offset+len)
  distinct : (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len).roots.toList.Nodup
  order : ∀ valid : 0 < (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len).roots.size,
      raw.selected ≠ (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len).roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder
        (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len)
  short : (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len).nodes.size < 65536

/-- Both active source and wildcard return packets are derived at one actual
protector state, including the distinct-allocation relation. -/
theorem after_protection
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
      (destination : DuplicatePrefixReturnPlaceInput.Input
        (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
          reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
      (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
      let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
      destination.id = input.contract.destination.id ∧
      TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag
        place (Storage.withCurrent #[] changed current) = .ok () after ∧
      Nonempty (S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id
        reference.tracker.global.nextPointerTag borrowFrame) ∧
      Nonempty (SourcePacket id tag address len reference after.machine) := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,destId,_destEntry,
    protect,⟨returnPacket⟩⟩ :=
    S02ConcreteSourceWildcardReturnPacket.after_protection id tag address len count input
      nonempty different returnWildcard
  have sourceId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have separate : destination.id ≠ reference.id := by
    rw [destId,sourceId]
    exact Ne.symm different
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  obtain ⟨child,node,raw,tracker,enabled,live,tagged,present,same,hidden,runtime,
    ⟨positive⟩,activity,distinct,order,short⟩ :=
    S02SeparateDestinationSourceFullAtWitness.source_packet id tag address len input reference
      firstFresh destination separate secondFresh tree updated changed owned
  let sourcePacket : SourcePacket id tag address len reference after.machine := {
    raw := raw
    child := child
    node := node
    tracker := tracker
    enabled := enabled
    live := live
    tagged := tagged
    present := present
    same := same
    hidden := hidden
    runtime := runtime
    positive := positive
    activity := activity
    distinct := distinct
    order := order
    short := short }
  exact ⟨reference,firstFresh,destination,secondFresh,tree,updated,destId,protect,
    ⟨returnPacket⟩,⟨sourcePacket⟩⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardBothPacket

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardBothPacket.after_protection) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard both-packet dependency {dependency}"
