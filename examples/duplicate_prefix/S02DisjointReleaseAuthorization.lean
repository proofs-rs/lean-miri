import duplicate_prefix.S02DisjointReleaseFrame
import duplicate_prefix.GeneralBorrowBothProtectorRelease

namespace DuplicatePrefix.S02DisjointReleaseAuthorization
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowSnapshotWildcardRangeBoth (authorization_locations)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem row_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (row : Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row {tree with locations := locations}
      location protections source selected maximum) := by
  obtain ⟨row⟩ := row
  refine ⟨{
    wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
    cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor equal
    obtain ⟨normal⟩ := row.normal anchor equal
    exact ⟨{component := normal.component,permissions := normal.permissions}⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := row.callbacks position valid different
    exact ⟨support,authorization_locations tree locations location protections _ _ _ _ support read,
      authorization_locations tree locations location protections _ _ _ _ support write⟩

/-- Actual successful source release preserves full authorization on a disjoint
return window. Its success is derived from the source's current capability. -/
theorem positive (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (source : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some anchor) (some selected) maximum offset len)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write offset (offset+len))
    (target targetSelected : Option UniIndex) (targetMaximum : Option BorTag) (targetOffset targetLen : UInt64)
    (destination : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags target targetSelected targetMaximum targetOffset targetLen)
    (disjoint : (offset+len).toNat ≤ targetOffset.toNat ∨ (targetOffset+targetLen).toNat ≤ offset.toNat) :
    let actual := tree.releaseProtector tag global.protectedTags
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree global.protectedTags target targetSelected targetMaximum targetOffset targetLen) := by
  obtain ⟨success,afterRuntime,sourcePositive,sourceActive,shape,capacity⟩ :=
    GeneralBorrowBothProtectorRelease.release tree global runtime tag anchor selected maximum offset len
      source node present hidden tagged distinct order short active
  let actual := tree.releaseProtector tag global.protectedTags
  have kept := S02DisjointReleaseFrame.release tree global.protectedTags tag anchor anchor node tagged present hidden
    offset (offset+len) active active
    (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location global.protectedTags target targetSelected targetMaximum))
    targetOffset (targetOffset+targetLen) disjoint destination.rows runtime.formed.well
  refine ⟨success,afterRuntime,⟨⟨destination.positive,?_,?_,?_,?_⟩⟩⟩
  · rw [capacity]; exact destination.bounds
  · intro index equal
    obtain ⟨targetNode,found⟩ := destination.sourcePresent index equal
    refine ⟨targetNode,?_⟩
    change actual.tree.nodes.get index = some targetNode
    rw [congrArg BorrowTree.nodes shape]
    exact found
  · intro absent
    rw [congrArg BorrowTree.roots shape]
    exact destination.wildcardRoot absent
  · rw [shape]
    intro position valid positive beforeUpper afterLower
    exact row_locations tree _ _ global.protectedTags target targetSelected targetMaximum
      (kept position valid positive beforeUpper afterLower)

end DuplicatePrefix.S02DisjointReleaseAuthorization

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02DisjointReleaseAuthorization.positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved disjoint release authorization dependency {dependency}"
