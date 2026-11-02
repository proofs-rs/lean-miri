import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.GeneralBorrowRawDefaultResources
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot

namespace DuplicatePrefix.S02SameDestinationAcceptedDefaultLookup
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

/-- Exact typed FnEntry preserves every old tag lookup. Only the fresh tag
itself changes, irrespective of allocator append/reuse. -/
theorem preserved (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global) :
    let finalTree := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    ∀ oldTag,tracker.global.nextPointerTag ≠ oldTag → finalTree.indexOfTag oldTag = tree.indexOfTag oldTag := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,unheld⟩ :=
    GeneralBorrowDefaultTagAllocation.prepare tree tracker.global input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration registeredRuntime
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
  let depth := GeneralBorrowStructuralHistoryDefault.depth accessed.tree afterRuntime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot accessed.tree afterRuntime.formed.toState input.parent parentNode parentPresent room
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth afterRuntime.formed.children
    afterRuntime.formed.covered input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent
    freshAfter slot input.offset input.len nonzero afterRuntime.formed.well afterRuntime.formed.fits afterPositive.bounds
  dsimp only
  intro oldTag different
  have same := metadata.oldLookup oldTag different
  change ((GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree).indexOfTag oldTag = _
  change (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree input.parentTag tracker.global.nextPointerTag input.offset input.len).indexOfTag oldTag = _
  rw [same]
  unfold BorrowTree.indexOfTag
  rw [contract.tags]

/-- Preserve any already mapped tag, including aliases of an original parent. -/
theorem mapped (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (tag : BorTag) (query : UniIndex) (tagged : tree.indexOfTag tag = some query) :
    (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree.indexOfTag tag = some query := by
  have fresh := GeneralBorrowParentTagInvariant.fresh tree tracker.global runtime
  have missing : tree.indexOfTag tracker.global.nextPointerTag = none := by
    simp [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tracker.global.nextPointerTag fresh]
  have different : tracker.global.nextPointerTag ≠ tag := by
    intro same
    rw [←same,missing] at tagged
    cases tagged
  rw [preserved tree tracker runtime input tag different]
  exact tagged

end DuplicatePrefix.S02SameDestinationAcceptedDefaultLookup

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedDefaultLookup.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
