import duplicate_prefix.S02ConcreteSourceWildcardInstalled
import duplicate_prefix.S02ConcreteSourceWildcardBothPacket

namespace DuplicatePrefix.S02ConcreteSourceWildcardInstalledBoth
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Exact installed call with active concrete source and wildcard return packets. -/
theorem enters_both
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
      let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
        destination.tracker.global.nextPointerTag
      let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
      destination.id = input.contract.destination.id ∧
      Nonempty (S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id
        reference.tracker.global.nextPointerTag borrowFrame) ∧
      Nonempty (S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference after.machine) := by
  obtain ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual,destId,
    ⟨returnPacket⟩⟩ := S02ConcreteSourceWildcardInstalled.enters
      id tag address len count input nonempty different returnWildcard
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
  let sourcePacket : S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference after.machine := {
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
  exact ⟨reference,firstFresh,destination,secondFresh,tree,updated,actual,destId,
    ⟨returnPacket⟩,⟨sourcePacket⟩⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardInstalledBoth

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardInstalledBoth.enters_both) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard installed-both dependency {dependency}"
