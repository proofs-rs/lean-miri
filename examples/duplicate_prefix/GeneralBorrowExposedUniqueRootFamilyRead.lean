import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilySeed
import duplicate_prefix.GeneralBorrowExposedWildcardStoredRead
import duplicate_prefix.GeneralBorrowNormalExposureTodo
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Exact Unique levels make this parentless leaf family's real exposure cache
independent of protector membership, including a fresh Strong registration. -/
theorem coherent (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (protections : ProtectedTags) :
    GeneralBorrowExposureCardinality.LocationCoherent tree location protections := by
  apply GeneralBorrowNormalExposureTodo.coherent_congr location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location global.protectedTags)
    (GeneralBorrowExposureCardinality.effective location protections) family.coherent
  intro index node present
  obtain ⟨actual,found,parentless,leaf,exposed,unique,cache⟩ := family.leaves index (family.allNodes index node present)
  have equal := Option.some.inj (found.symm.trans present)
  subst node
  simp only [GeneralBorrowExposureCardinality.effective,unique,Option.getD_some,GeneralBorrowWildcardLeaf.unique,
    Permission.strongestAllowedLocalAccess]

/-- Actual full-range wildcard parent Read retains the entire family exactly;
registration cannot turn it into a failing foreign Unique access. -/
theorem ranged (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (protections : ProtectedTags) (room : tree.nodes.size<65536) :
    let read := tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed
    read.status=.Completed ∧ read.tree=tree := by
  cases roots with
  | nil => exact False.elim (family.nonempty rfl)
  | cons head extras =>
    obtain ⟨headNode,headPresent,headParent,headLeaf,headExposed,headUnique,headCache⟩ := family.leaves head (by simp)
    let nodes : UniIndex→TreeNode := fun index => (tree.nodeAt index).getD headNode
    apply GeneralBorrowExposedWildcardStoredRead.ranged tree location protections head headNode extras nodes
      (fun _=>GeneralBorrowWildcardLeaf.unique) capacity family.nonzero family.locations family.rootsEq headPresent headLeaf headExposed headUnique
      (coherent capacity global tree location (head::extras) family protections) room
    intro root member
    obtain ⟨node,present,parentless,leaf,exposed,unique,cache⟩ := family.leaves root (by simp [member])
    have same : nodes root=node := by simp only [nodes,present,Option.getD_some]
    refine ⟨?_,?_,?_,unique,?_⟩
    · rw [same];exact present
    · rw [same];exact leaf
    · rw [same];exact exposed
    · rw [same]
      simp [GeneralBorrowExposureCardinality.effective,unique,GeneralBorrowWildcardLeaf.unique,
        Permission.strongestAllowedLocalAccess,GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead]
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyRead
