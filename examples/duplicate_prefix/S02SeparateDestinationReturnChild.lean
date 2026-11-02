import duplicate_prefix.S03ReturnChildMetadata
import duplicate_prefix.S03ReturnProtectionRaw

namespace DuplicatePrefix.S02SeparateDestinationReturnChild
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual concrete return constructor and subsequent Write leave a
present hidden child of its original parent in the final written tree. -/
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
    ∃ parent child node,
      written.indexOfTag tag = some parent ∧
      written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
      written.nodeAt child = some node ∧
      node.tag = input.tracker.global.nextPointerTag ∧
      node.parent = some parent ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ :=
    S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  have metadata := S03ReturnChildMetadata.run input.entry.allocation.extra input.tracker ({} : FrameState)
    input.id runtime raw
  simp only [parentTag,offset,length] at metadata
  obtain ⟨parentTagged,child,node,childTagged,present,same,edge,leaf,hidden⟩ := metadata
  exact ⟨raw.parent,child,node,parentTagged,childTagged,present,same,edge,leaf,hidden⟩

end
end DuplicatePrefix.S02SeparateDestinationReturnChild

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationReturnChild.run) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination return child dependency {dependency}"
