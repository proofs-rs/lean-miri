import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyHistory
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyRows
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

theorem node_tag_below (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (roots : List UniIndex) (family : Family capacity global tree location roots)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index=some node) :
    node.tag.value<global.nextPointerTag.value := by
  have tagged := family.structural.allocator.nodeTags index node present
  unfold UniKeyMap.get at tagged
  cases looked : tree.tagMapping.mapping.find? (fun row=>row.1==node.tag) with
  | none => simp [looked] at tagged
  | some row =>
    have key : row.1=node.tag := by simpa only [beq_iff_eq] using Array.find?_some looked
    have bound := family.highWater row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some looked))
    rw [key] at bound
    exact bound

/-- Allocator freshness for the current tag and every later prospective tag. -/
theorem fresh_above (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (roots : List UniIndex) (family : Family capacity global tree location roots)
    (tag : BorTag) (above : global.nextPointerTag.value≤tag.value) :
    GeneralBorrowTagMap.Fresh tree.tagMapping tag := by
  intro row member equal
  have bound := family.highWater row (Array.mem_toList_iff.mpr member)
  rw [equal] at bound
  have first := UInt64.lt_iff_toNat_lt.mp bound
  have second := UInt64.le_iff_toNat_le.mp above
  omega

/-- The graph/cache/allocator portion of positive-wildcard Base, separated
from its physical caller and compiler metadata. -/
structure Rows (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (roots : List UniIndex) (protections : ProtectedTags) where
  head : UniIndex
  headNode : TreeNode
  extraRoots : List UniIndex
  nodes : UniIndex→TreeNode
  split : roots=head::extraRoots
  locations : tree.locations=RangeMapNonempty.homogeneous capacity location
  rootsEq : tree.roots=(head::extraRoots).toArray
  headPresent : tree.nodes.get head=some headNode
  headLeaf : headNode.children=#[]
  headExposed : headNode.isExposed=true
  headStored : location.perms.get head=some GeneralBorrowWildcardLeaf.unique
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections
  data : ∀ root∈extraRoots,tree.nodes.get root=some (nodes root) ∧ (nodes root).children=#[] ∧
    (nodes root).isExposed=true ∧ location.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
    GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) .Read=true
  allLeaves : ∀ root∈head::extraRoots,∃ node,tree.nodeAt root=some node ∧ node.children=#[] ∧
    node.isExposed=true ∧ location.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
    node.tag.value≤global.nextPointerTag.value
  tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag
  noFree : tree.tagMapping.deassigned.back?=none
  structural : GeneralBorrowStructuralHistoryState.State tree
  mapAligned : tree.tagMapping.mapping.size=tree.nodes.data.size

/-- Generated families supply the exposed Unique rows required by Base under
its actual registered protector table; no row certificate is an input. -/
theorem rows (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (roots : List UniIndex) (family : Family capacity global tree location roots) (protections : ProtectedTags) :
    Nonempty (Rows capacity global tree location roots protections) := by
  cases roots with
  | nil => exact False.elim (family.nonempty rfl)
  | cons head extras =>
    obtain ⟨headNode,present,parentless,leaf,exposed,unique,cache⟩ := family.leaves head (by simp)
    let nodes : UniIndex→TreeNode := fun index=>(tree.nodeAt index).getD headNode
    refine ⟨⟨head,headNode,extras,nodes,rfl,family.locations,family.rootsEq,present,leaf,exposed,unique,
      GeneralBorrowExposedUniqueRootFamilyRead.coherent capacity global tree location (head::extras) family protections,
      ?_,?_,fresh_above capacity global tree location (head::extras) family global.nextPointerTag (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)),
      family.noFree,family.structural,family.aligned⟩⟩
    · intro root member
      obtain ⟨node,found,parentless,leaf,exposed,unique,cache⟩ := family.leaves root (by simp [member])
      have same : nodes root=node := by simp only [nodes,found,Option.getD_some]
      refine ⟨?_,?_,?_,unique,?_⟩
      · rw [same];exact found
      · rw [same];exact leaf
      · rw [same];exact exposed
      · rw [same]
        simp [GeneralBorrowExposureCardinality.effective,unique,GeneralBorrowWildcardLeaf.unique,
          Permission.strongestAllowedLocalAccess,GeneralBorrowExposureCardinality.supports,
          GeneralBorrowExposureAncestorFold.supportsRead]
    · intro root member
      obtain ⟨node,found,parentless,leaf,exposed,unique,cache⟩ := family.leaves root member
      have below := node_tag_below capacity global tree location (head::extras) family root node found
      exact ⟨node,found,leaf,exposed,unique,UInt64.le_iff_toNat_le.mpr (by have b:=UInt64.lt_iff_toNat_lt.mp below;omega)⟩
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyRows
