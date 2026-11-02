import duplicate_prefix.S02ConcreteSourceReleasePacket
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.S02SeparateDestinationSourceRuntime

namespace DuplicatePrefix.S02SeparateDestinationSourceFullAtWitness
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Complete active source packet on an exact post-return-protection state.
The full Both capability comes from the original positive call input; the
source child and its ownership metadata come from real FnEntry. -/
theorem source_packet
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
    (different : destination.id ≠ reference.id)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :
    let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker firstFresh reference.id reference.entry tag reference.offset len
    let after := S04ProtectUninit.finished current place destination #[] frame borrowFrame secondFresh tree updated
    let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len
    let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
    ∃ (child : UniIndex) (node : TreeNode)
      (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
      (tracker : MachineHooks.BorrowState),
      after.machine.borrowTracker = some tracker ∧
      after.machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some child ∧
      sourceEntry.allocation.extra.nodeAt child = some node ∧
      node.tag = reference.tracker.global.nextPointerTag ∧ node.isExposed = false ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        tracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
        reference.offset (reference.offset+len) ∧
      sourceEntry.allocation.extra.roots.toList.Nodup ∧
      (∀ valid : 0 < sourceEntry.allocation.extra.roots.size,
        raw.selected ≠ sourceEntry.allocation.extra.roots[0] →
          GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra) ∧
      sourceEntry.allocation.extra.nodes.size < 65536 := by
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  obtain ⟨same,raw,parent,offset,length,_source,_selected,_maximum,runtimeInitial⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference
      input.contract.runtime input.contract.resources
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have headroom : reference.entry.allocation.extra.nodes.size+1 < 65536 := by
    have room := input.contract.resources.nodeRoom (reference.id,reference.entry) member
    have room' : reference.entry.allocation.extra.nodes.size+16 < 65536 := by simpa only using room
    omega
  obtain ⟨child,node,lookup,present,sameTag,hidden,runtime,⟨positive⟩,active,roots,order,short⟩ :=
    S02ConcreteSourceReleasePacket.release_ready reference.entry.allocation.extra reference.tracker
      ({} : FrameState) reference.id runtimeInitial raw headroom
  have treeEq : sourceTree = GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker raw.parentTag raw.offset raw.len := by rw [parent,offset,length]
  rw [←treeEq] at lookup present runtime positive active roots order short
  obtain ⟨_sourceChild,_sourceRaw,_same,_parent,_offset,_length,sourceLive,enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have trackerEq : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans enabled)
  have globalEq : destination.tracker.global =
      TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh :=
    congrArg MachineHooks.BorrowState.global trackerEq
  change DuplicatePrefixBorrowContract.RuntimeFacts sourceTree
    (TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh) at runtime
  change DuplicatePrefixBorrowAuthorization.Positive sourceTree
    (TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh).protectedTags
    (some child) (some raw.selected) raw.maximum raw.offset raw.len at positive
  rw [←globalEq] at runtime positive
  have positiveCurrent : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      destination.tracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len := by
    change DuplicatePrefixBorrowAuthorization.Positive sourceTree destination.tracker.global.protectedTags
      (some child) (some raw.selected) raw.maximum reference.offset len
    simpa only [offset,length] using positive
  obtain ⟨sourceTracker,trackerAfter,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      frame borrowFrame secondFresh tree updated reference.id sourceEntry different sourceLive runtime
      (some child) (some raw.selected) raw.maximum reference.offset len positiveCurrent
  obtain ⟨runtimeTracker,runtimeTrackerAfter,_runtimeLive,runtimeAfter⟩ :=
    S02SeparateDestinationSourceRuntime.runtime_after_protect current place destination #[]
      frame borrowFrame secondFresh tree updated reference.id sourceEntry different sourceLive runtime
  have sameTracker : runtimeTracker = sourceTracker :=
    Option.some.inj (runtimeTrackerAfter.symm.trans trackerAfter)
  rw [sameTracker] at runtimeAfter
  have sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
      reference.offset (reference.offset+len) := by
    change GeneralBorrowFreshActiveWithin.ActiveWithin sourceTree child .Write
      reference.offset (reference.offset+len)
    simpa only [offset,length] using active
  exact ⟨child,node,raw,sourceTracker,trackerAfter,liveAfter,lookup,present,sameTag,hidden,
    runtimeAfter,⟨positiveAfter⟩,sourceActive,roots,order,short⟩

end
end DuplicatePrefix.S02SeparateDestinationSourceFullAtWitness

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceFullAtWitness.source_packet) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination full source-witness dependency {dependency}"
