import duplicate_prefix.S02DisjointSharedRuntime
import duplicate_prefix.S02DisjointReadOnlyPositive
import duplicate_prefix.GeneralBorrowRawSharedFnEntryArgument
import duplicate_prefix.GeneralBorrowFreshRegistration

namespace DuplicatePrefix.S02DisjointSharedFnEntry
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The real shared helper FnEntry, including Strong registration, Read,
protected Frozen construction and Read SIFA, preserves a disjoint destination.
The fresh protector's effect is derived from current runtime highwater. -/
theorem literal (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowRawSharedFnEntry.Input tree global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (destination : Positive tree global.protectedTags source selected maximum lower width) :
    let registered := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read registered.1.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    GeneralBorrowRawSharedFnEntry.operation tree global frame allocation input.parentTag input.offset input.len .VisitChildrenOfAccessed =
      .ok ⟨registered.1,registered.2,global.nextPointerTag,read,child⟩ ∧ read.status = .Completed ∧ child.outcome = .ok () ∧
    Nonempty (Positive child.tree registered.1.protectedTags source selected maximum lower width) := by
  obtain ⟨allocated,_held,_frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ := GeneralBorrowFnEntryReadRegistration.prepare tree global frame allocation
    input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registered := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  have complete := GeneralBorrowForestTagHighWater.complete tree global.protectedTags global.nextPointerTag runtime.below runtime.formed.allocator.nodeTags
  have nodeFresh := (GenericFunctionTagFormation.fresh_above tree global.protectedTags global.nextPointerTag global.nextPointerTag
    complete (Nat.le_refl _)).2.1
  obtain ⟨registeredDestination⟩ := GeneralBorrowFreshRegistration.positive tree global.protectedTags global.nextPointerTag .StrongProtector
    nodeFresh source selected maximum lower width destination
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read registered.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree registered.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨afterDestination⟩ := S02DisjointReadOnlyPositive.positive_from_source_contract tree input.parentTag input.parent input.selected input.maximum
    input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registered.1.protectedTags .VisitChildrenOfAccessed
    source selected maximum lower width registeredDestination runtime.formed.well input.positive.bounds outside contract.capacity
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have positive := input.positive.positive;rw [zero] at positive;contradiction
  obtain ⟨childDone,positive⟩ := S02DisjointSharedRuntime.construct accessed.tree registered.1 afterRuntime input.parentTag global.nextPointerTag
    input.parent parentNode tagged parentPresent freshAfter room true input.offset input.len nonzero afterPositive.bounds
    source selected maximum lower width outside afterDestination
  refine ⟨?_,contract.completed,childDone,positive⟩
  simp only [GeneralBorrowRawSharedFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
  rfl

/-- Destination transport on the literal tree installed by typed shared helper
argument passing; caller retag mode and frame proofs do not affect that tree. -/
theorem final_tree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global) (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (destination : Positive tree tracker.global.protectedTags source selected maximum lower width) :
    Nonempty (Positive (GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len)
      (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).protectedTags source selected maximum lower width) := by
  exact (literal tree tracker.global frame allocation runtime input source selected maximum lower width outside destination).2.2.2

end DuplicatePrefix.S02DisjointSharedFnEntry

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02DisjointSharedFnEntry.literal,``DuplicatePrefix.S02DisjointSharedFnEntry.final_tree] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
