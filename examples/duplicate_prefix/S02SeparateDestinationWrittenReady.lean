import duplicate_prefix.S03ReturnWrittenGeometry
import duplicate_prefix.S03ReturnProtectionRaw

namespace DuplicatePrefix.S02SeparateDestinationWrittenReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Root uniqueness, parent-tag order and node headroom of the literal
concrete return-child Write, derived from current allocation resources. -/
theorem run {before : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
      input.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.roots.toList.Nodup ∧ GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
    written.nodes.size < 65536 := by
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ :=
    S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  have geometry := S03ReturnWrittenGeometry.run input.entry.allocation.extra input.tracker
    ({} : FrameState) input.id runtime raw order headroom
  have protectedOrder := GeneralBorrowRawFnEntryOrder.order input.entry.allocation.extra input.tracker
    ({} : FrameState) input.id runtime raw order
  simp only [parentTag,offset,length] at geometry protectedOrder
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
    input.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have writeFrame := GeneralBorrowFreshReadFrame.frame tree (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed
  have afterOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder written := by
    unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder
    rw [congrArg BorrowTree.nodes writeFrame]
    exact protectedOrder
  exact ⟨geometry.2.1,afterOrder,geometry.2.2⟩

end
end DuplicatePrefix.S02SeparateDestinationWrittenReady

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationWrittenReady.run) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination written-ready dependency {dependency}"
