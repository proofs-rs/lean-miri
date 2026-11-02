import duplicate_prefix.S02DisjointReadFrame
import duplicate_prefix.S02ConstructorOutsideRow
import duplicate_prefix.GeneralBorrowReadRowRange
import duplicate_prefix.GeneralBorrowFreshReadFrame

namespace DuplicatePrefix.S02DisjointReadOnlyPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The standard source-window Read/Write contract supplies the structural frame
and capacity facts, so a disjoint destination's full Positive capability
survives the access. In the FnEntry path this contract is already proved by
`GeneralBorrowConcreteRowReadRange.access_runtime`. -/
theorem positive_from_source_contract (tree : BorrowTree) (tag : BorTag)
    (anchor sourceSelected : UniIndex) (sourceMaximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (destinationSource destinationSelected : Option UniIndex)
    (destinationMaximum : Option BorTag) (lower destinationLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections
      destinationSource destinationSelected destinationMaximum lower destinationLen)
    (well : tree.locations.WellFormed)
    (sourceBounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.bytes.toNat + len.bytes.toNat ≤ lower.toNat ∨
      (lower+destinationLen).toNat ≤ offset.bytes.toNat)
    (capacity : (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode).tree.locations.size = tree.locations.size) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive
      (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode).tree
      protections destinationSource destinationSelected destinationMaximum lower destinationLen) := by
  let result := tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode
  have treeEq : result.tree = {tree with locations := result.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame tree (.concrete tag) offset len kind protections mode
  have nodes := congrArg BorrowTree.nodes treeEq
  have roots := congrArg BorrowTree.roots treeEq
  have kept := S02DisjointReadFrame.concrete tree tag anchor tagPresent offset len kind protections mode
    (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections
      destinationSource destinationSelected destinationMaximum)) lower (lower+destinationLen) well sourceBounds outside positive.rows
  have rows : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row result.tree location protections
      destinationSource destinationSelected destinationMaximum)) lower (lower+destinationLen) result.tree.locations := by
    rw [treeEq]
    intro position valid nonempty start stop
    obtain ⟨row⟩ := kept position valid nonempty start stop
    exact S02ConstructorOutsideRow.context tree tree.tagMapping _ _ protections destinationSource destinationSelected destinationMaximum row
  refine ⟨{
    positive := positive.positive,
    bounds := ?_,
    sourcePresent := ?_,
    wildcardRoot := ?_,
    rows := ?_}⟩
  · rw [capacity]
    exact positive.bounds
  · intro anchor same
    unfold BorrowTree.nodeAt
    rw [nodes]
    exact positive.sourcePresent anchor same
  · intro same
    rw [roots]
    exact positive.wildcardRoot same
  · exact rows

end DuplicatePrefix.S02DisjointReadOnlyPositive

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointReadOnlyPositive.positive_from_source_contract) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
