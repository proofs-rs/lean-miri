import duplicate_prefix.S03ReturnWrittenGeometry
import duplicate_prefix.S03ReturnTagFrame
import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.ConcreteEmptyRuntimeEntry

namespace DuplicatePrefix.S02SeparateDestinationWrittenShape
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual concrete return child and subsequent Write retain the parent
tag and physical tree capacity. These are derived from the current Input and
local headroom, not assumed of the future written state. -/
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
    written.locations.size = input.entry.allocation.extra.locations.size ∧
    written.indexOfTag tag = input.entry.allocation.extra.indexOfTag tag := by
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ :=
    S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  have geometry := S03ReturnWrittenGeometry.run input.entry.allocation.extra input.tracker ({} : FrameState)
    input.id runtime raw order headroom
  have oldTags := S03ReturnTagFrame.run input.entry.allocation.extra input.tracker ({} : FrameState)
    input.id runtime raw
  simp only [parentTag,offset,length] at geometry oldTags
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,parent,_,tagged⟩ := binding
  have different := S03EmptyReturnConstructorFacts.fresh_ne input.entry.allocation.extra
    input.tracker.global.nextPointerTag tag parent
    (ConcreteEmptyRuntimeEntry.counter_fresh _ _ runtime.below) tagged
  exact ⟨geometry.1,oldTags tag different⟩

end
end DuplicatePrefix.S02SeparateDestinationWrittenShape

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationWrittenShape.run) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination written-shape dependency {dependency}"
