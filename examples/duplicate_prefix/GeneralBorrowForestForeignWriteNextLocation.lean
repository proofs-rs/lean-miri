import duplicate_prefix.GeneralBorrowForestForeignAccess
import duplicate_prefix.GeneralBorrowFreshSharedPaths

namespace DuplicatePrefix.GeneralBorrowForestForeignWriteNextLocation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowForestForeignAccess (LocationData)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Data-only next-location rule for leaf attachment. Old supporting subtrees
are retained even though the selected concrete source changes to its new child.
All fields refer to graph, cache and ownership; no operation outcome is a
premise. Actual constructors provide these fields through their separate
metadata, ownership and range-origin bridges. -/
theorem attach_location (before after : BorrowTree) (initial final : LocationTree) (protections : ProtectedTags)
    (parent child primary : UniIndex) (extras : List UniIndex)
    (data : LocationData before initial protections parent primary extras .Write)
    (newOwner : GeneralBorrowRange.LocationOwned after protections child .Write final)
    (paths : (source_normal_projection after final protections).topology.ancestorPath child.toNat =
      child.toNat :: (source_normal_projection before initial protections).topology.ancestorPath parent.toNat)
    (fresh : ∀ index node, before.nodeAt index = some node → index ≠ child)
    (otherNodes : ∀ index oldNode, before.nodeAt index = some oldNode → index ≠ parent →
      ∃ next, after.nodeAt index = some next ∧ next.children = oldNode.children)
    (unexposed : ∀ index node, after.nodeAt index = some node → node.isExposed = false)
    (cache : final.exposedCache = initial.exposedCache) :
    ∃ next : LocationData after final protections child primary extras .Write, next.region.support = data.region.support := by
  have notParent : ∀ query, data.region.support query → query ≠ parent := by
    intro query member equal
    subst query
    exact data.foreignGraph parent member
      (GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection before initial protections).topology parent.toNat)
  have notChild : ∀ query, data.region.support query → query ≠ child := by
    intro query member
    obtain ⟨node,present⟩ := data.region.present query member
    exact fresh query node present
  have foreignGraph : ∀ query, data.region.support query →
      query.toNat ∉ (source_normal_projection after final protections).topology.ancestorPath child.toNat := by
    intro query member
    rw [paths]
    intro contains
    rcases List.mem_cons.mp contains with same | previous
    · exact notChild query member (GeneralBorrowNodeUpdate.index_injective query child same)
    · exact data.foreignGraph query member previous
  let region : GeneralBorrowWildcardSubtreeRegion.Region after final .Write protections := {
    support := data.region.support
    present := by
      intro query member
      obtain ⟨oldNode,present⟩ := data.region.present query member
      obtain ⟨next,lookup,children⟩ := otherNodes query oldNode present (notParent query member)
      exact ⟨next,lookup⟩
    children := by
      intro query node member present childIndex childMember
      obtain ⟨oldNode,oldPresent⟩ := data.region.present query member
      obtain ⟨next,lookup,children⟩ := otherNodes query oldNode oldPresent (notParent query member)
      have equal : node = next := Option.some.inj (present.symm.trans lookup)
      subst node
      rw [children] at childMember
      exact data.region.children query oldNode member oldPresent childIndex childMember
    unexposed := by intro query node member present;exact unexposed query node present
    zero := by intro query member;rw [cache];exact data.region.zero query member
    owned := by
      intro query node member present
      exact GeneralBorrowForeignOwnerRegion.foreign after final protections child query node .Write present newOwner.2 (foreignGraph query member) }
  have pathNonempty : (source_normal_projection before initial protections).topology.ancestorPath parent.toNat ≠ [] := by
    intro empty
    have member := GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection before initial protections).topology parent.toNat
    rw [empty] at member
    exact List.not_mem_nil member
  have rootPath : ((source_normal_projection after final protections).topology.ancestorPath child.toNat).getLast! = primary.toNat := by
    rw [paths]
    cases path : (source_normal_projection before initial protections).topology.ancestorPath parent.toNat with
    | nil => exact False.elim (pathNonempty path)
    | cons first rest =>
      have root := data.rootPath
      rw [path] at root
      simpa only [List.getLast!_cons_eq_getLastD,List.getLastD_cons] using root
  obtain ⟨forest⟩ := newOwner.1
  exact ⟨{
    forest := forest
    owned := newOwner.2
    rootPath := rootPath
    region := region
    supported := data.supported
    foreignGraph := foreignGraph },rfl⟩

end DuplicatePrefix.GeneralBorrowForestForeignWriteNextLocation
