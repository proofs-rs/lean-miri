import duplicate_prefix.GeneralBorrowRawFnEntryHidden
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.S02FnEntryOldLookup
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

/-- Exact typed FnEntry preserves every old tag lookup. Only the fresh tag
itself changes, irrespective of allocator append/reuse. -/
theorem preserved (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    ∀ oldTag,tracker.global.nextPointerTag ≠ oldTag → finalTree.indexOfTag oldTag = tree.indexOfTag oldTag := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  let depth := GeneralBorrowStructuralHistoryMutable.depth accessed.tree afterRuntime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot accessed.tree afterRuntime.formed.toState input.parent parentNode parentPresent room
  have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth afterRuntime.formed.children
    afterRuntime.formed.covered input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent
    freshAfter slot input.offset input.len nonzero afterRuntime.formed.well afterRuntime.formed.fits afterPositive.bounds
  dsimp only
  intro oldTag different
  have same := metadata.oldLookup oldTag different
  change (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len).indexOfTag oldTag = _
  change (GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree input.parentTag tracker.global.nextPointerTag input.offset input.len).indexOfTag oldTag = _
  rw [same]
  unfold BorrowTree.indexOfTag
  rw [contract.tags]

end DuplicatePrefix.S02FnEntryOldLookup

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02FnEntryOldLookup.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
