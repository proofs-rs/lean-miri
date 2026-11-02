import duplicate_prefix.S02DisjointReadAuthorization
import duplicate_prefix.GeneralBorrowConcreteRowReadRange

namespace DuplicatePrefix.S02DisjointReadPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The standard source-window Read contract supplies the structural frame
and capacity facts, so a disjoint destination's full Positive capability
survives the Read. In the FnEntry path this contract is already proved by
`GeneralBorrowConcreteRowReadRange.access_runtime`. -/
theorem positive_from_source_contract (tree : BorrowTree) (tag : BorTag)
    (anchor sourceSelected : UniIndex) (sourceMaximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (destinationSource destinationSelected : Option UniIndex)
    (destinationMaximum : Option BorTag) (lower destinationLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree protections
      destinationSource destinationSelected destinationMaximum lower destinationLen)
    (well : tree.locations.WellFormed)
    (sourceBounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.bytes.toNat + len.bytes.toNat ≤ lower.toNat ∨
      (lower+destinationLen).toNat ≤ offset.bytes.toNat)
    (sourceContract : GeneralBorrowConcreteRowReadRange.Contract tree protections
      anchor sourceSelected sourceMaximum offset.bytes (offset.bytes+len.bytes)
      (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive
      (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode).tree
      protections destinationSource destinationSelected destinationMaximum lower destinationLen) := by
  let result := tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode
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
  have rows : OwnedOn (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Row result.tree location protections
        destinationSource destinationSelected destinationMaximum))
      lower (lower+destinationLen) result.tree.locations :=
    S02DisjointReadAuthorization.row tree tag anchor tagPresent offset len protections mode destinationSource destinationSelected
      destinationMaximum lower (lower+destinationLen) well sourceBounds outside positive.rows treeEq
  refine ⟨{
    positive := positive.positive,
    bounds := ?_,
    sourcePresent := ?_,
    wildcardRoot := ?_,
    rows := ?_}⟩
  · rw [sourceContract.capacity]
    exact positive.bounds
  · intro anchor same
    unfold BorrowTree.nodeAt
    rw [sourceContract.nodes]
    exact positive.sourcePresent anchor same
  · intro same
    rw [sourceContract.roots]
    exact positive.wildcardRoot same
  · exact rows

end DuplicatePrefix.S02DisjointReadPositive

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointReadPositive.positive_from_source_contract) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
