import duplicate_prefix.S02WildcardSameDestinationReadFrame
import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeRuntime
import duplicate_prefix.S02ConstructorOutsideRow
import duplicate_prefix.GeneralBorrowConcreteRowReadRange

namespace DuplicatePrefix.S02WildcardSameDestinationRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual wildcard source Read derives its successful runtime contract and
preserves a disjoint owner's complete Positive capability. No operation success
or post-read permission is supplied as a premise. -/
theorem positive (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (destinationSource destinationSelected : Option UniIndex)
    (destinationMaximum : Option BorTag) (lower destinationLen : UInt64)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+destinationLen).toNat ≤ offset.toNat)
    (destinationPositive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      destinationSource destinationSelected destinationMaximum lower destinationLen) :
    let result := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
      .Read global.protectedTags .VisitChildrenOfAccessed
    GeneralBorrowSnapshotWildcardRangeBoth.Contract tree global.protectedTags offset (offset+len) result ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree global.protectedTags
        destinationSource destinationSelected destinationMaximum lower destinationLen) := by
  let protections := global.protectedTags
  let result := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  obtain ⟨sourceContract,afterRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access tree global runtime
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed offset len sourcePositive distinct short
    (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨sourceContract,afterRuntime,?_⟩
  have treeEq : result.tree = {tree with locations := result.tree.locations} := by
    have nodes := sourceContract.nodes
    have roots := sourceContract.roots
    have tags := sourceContract.tags
    change result.tree.nodes = tree.nodes at nodes
    change result.tree.roots = tree.roots at roots
    change result.tree.tagMapping = tree.tagMapping at tags
    cases tree with
    | mk oldTags oldNodes oldLocations oldRoots =>
      cases h : result.tree with
      | mk newTags newNodes newLocations newRoots =>
        rw [h] at tags nodes roots
        simp only [BorrowTree.mk.injEq]
        exact ⟨tags,nodes,True.intro,roots⟩
  have kept := S02WildcardSameDestinationReadFrame.wildcard tree (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections
      destinationSource destinationSelected destinationMaximum)) lower (lower+destinationLen) runtime.formed.well sourcePositive.bounds outside destinationPositive.rows
  have rows : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row result.tree location protections
      destinationSource destinationSelected destinationMaximum)) lower (lower+destinationLen) result.tree.locations := by
    rw [treeEq]
    intro position valid nonempty start stop
    obtain ⟨row⟩ := kept position valid nonempty start stop
    exact S02ConstructorOutsideRow.context tree tree.tagMapping _ _ protections destinationSource destinationSelected destinationMaximum row
  refine ⟨{
    positive := destinationPositive.positive,
    bounds := ?_,
    sourcePresent := ?_,
    wildcardRoot := ?_,
    rows := ?_}⟩
  · rw [sourceContract.capacity]
    exact destinationPositive.bounds
  · intro anchor same
    unfold BorrowTree.nodeAt
    rw [sourceContract.nodes]
    exact destinationPositive.sourcePresent anchor same
  · intro same
    rw [sourceContract.roots]
    exact destinationPositive.wildcardRoot same
  · exact rows

end DuplicatePrefix.S02WildcardSameDestinationRead

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardSameDestinationRead.positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
